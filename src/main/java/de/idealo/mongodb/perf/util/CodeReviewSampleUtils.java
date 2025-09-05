package de.idealo.mongodb.perf.util;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStream;
import java.lang.invoke.MethodHandles;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.security.DigestInputStream;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.text.Normalizer;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Formatter;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.StringJoiner;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;
import java.util.regex.MatchResult;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Java 8 compatible utility class for strings/regex/CSV/sizes/checksums/io/algorithms.
 *
 * <p><b>Review topics:</b> 모듈 분리, 스레드 안전성(Regex LRU 캐시), 국제화, 성능(DP/버퍼링),
 * 예외/Null 처리 일관성, CSV RFC4180 준수 범위 등.</p>
 *
 * <p>Requires Java 8.</p>
 */
public final class CodeReviewSampleUtils {

  // ---------- Constants / Patterns ----------
  private static final Charset DEFAULT_CHARSET = StandardCharsets.UTF_8;
  private static final Pattern WHITESPACE = Pattern.compile("\\s+");
  private static final Pattern NON_ALNUM = Pattern.compile("[^\\p{IsAlphabetic}\\p{IsDigit}]+");
  private static final Pattern COMBINING_MARKS = Pattern.compile("\\p{M}+");
  private static final Pattern CSV_NEEDS_QUOTE = Pattern.compile("[,\"]|\\R");
  private static final Pattern CSV_QUOTE = Pattern.compile("\"");
  private static final int DEFAULT_REGEX_CACHE_SIZE = 128;

  private static final String CLASS_NAME =
      MethodHandles.lookup().lookupClass().getSimpleName();

  private CodeReviewSampleUtils() { /* no instantiation */ }

  // ---------- Basic String Helpers ----------

  /** Returns true if s is null, empty, or only whitespace. */
  public static boolean isBlank(String s) {
    return s == null || s.trim().isEmpty();
  }

  /** Trim and collapse internal whitespace to a single space. */
  public static String normalizeWhitespace(String s) {
    if (s == null) return "";
    return WHITESPACE.matcher(s.trim()).replaceAll(" ");
  }

  /** NFC normalize (composed form) for consistent storage/compare. */
  public static String normalizeNFC(String s) {
    if (s == null) return "";
    return Normalizer.normalize(s, Normalizer.Form.NFC);
  }

  /** NFKC normalize (compatibility + composition). Often better for search. */
  public static String normalizeNFKC(String s) {
    if (s == null) return "";
    return Normalizer.normalize(s, Normalizer.Form.NFKC);
  }

  /**
   * Slugify a string:
   * 1) NFKD 분해 → 2) 결합부호 제거 → 3) 비영숫자 하이픈 → 4) 소문자/하이픈 정리.
   * 한국어는 전사 정책에 따라 원문이 유지될 수 있습니다.
   */
  public static String slugify(String input, Locale locale) {
    if (isBlank(input)) return "";
    String nfkd = Normalizer.normalize(input, Normalizer.Form.NFKD);
    String noMarks = COMBINING_MARKS.matcher(nfkd).replaceAll("");
    String hyph = NON_ALNUM.matcher(noMarks).replaceAll("-");
    String lowered = hyph.toLowerCase(locale == null ? Locale.ROOT : locale);
    String collapsed = lowered.replaceAll("-{2,}", "-");
    return trimHyphens(collapsed);
  }

  private static String trimHyphens(String s) {
    int start = 0, end = s.length();
    while (start < end && s.charAt(start) == '-') start++;
    while (end > start && s.charAt(end - 1) == '-') end--;
    return s.substring(start, end);
  }

  /** Truncate by Unicode code points, optionally appending ellipsis. */
  public static String truncateByCodePoints(String s, int maxCodePoints, String ellipsis) {
    Objects.requireNonNull(ellipsis, "ellipsis");
    if (s == null) return "";
    if (maxCodePoints < 0) throw new IllegalArgumentException("maxCodePoints < 0");
    int count = s.codePointCount(0, s.length());
    if (count <= maxCodePoints) return s;

    int target = Math.max(0, maxCodePoints - (ellipsis.isEmpty()
        ? 0
        : ellipsis.codePointCount(0, ellipsis.length())));
    int index = s.offsetByCodePoints(0, target);
    return s.substring(0, index) + ellipsis;
  }

  // ---------- Regex: LRU Pattern Cache & Helpers ----------

  /** Simple LRU cache for compiled Patterns. */
  public static final class RegexCache {
    private final Map<String, Pattern> cache;

    public RegexCache(final int maxSize) {
      if (maxSize <= 0) throw new IllegalArgumentException("maxSize must be > 0");
      this.cache = Collections.synchronizedMap(
          new LinkedHashMap<String, Pattern>(maxSize * 2, 0.75f, true) {
            @Override
            protected boolean removeEldestEntry(Map.Entry<String, Pattern> eldest) {
              return size() > maxSize;
            }
          }
      );
    }

    public Pattern get(String regex, int flags) {
      String key = regex + "||" + flags;
      Pattern p = cache.get(key);
      if (p == null) {
        p = Pattern.compile(regex, flags);
        cache.put(key, p);
      }
      return p;
    }
  }

  private static final RegexCache REGEX_CACHE = new RegexCache(DEFAULT_REGEX_CACHE_SIZE);

  public static Pattern cachedPattern(String regex) {
    return REGEX_CACHE.get(regex, 0);
  }

  public static List<String> findAll(String input, String regex) {
    if (input == null) return Collections.emptyList();
    Pattern p = cachedPattern(regex);
    Matcher m = p.matcher(input);
    List<String> out = new ArrayList<String>();
    while (m.find()) out.add(m.group());
    return out;
  }

  /**
   * Java 8 compatible "replaceAll with Function".
   * Example: replaceAllFunc("a1b2", "\\d", mr -> "[" + mr.group() + "]") => "a[1]b[2]"
   */
  public static String replaceAllFunc(String input, String regex, Function<MatchResult, String> replacer) {
    if (input == null) return "";
    Matcher m = cachedPattern(regex).matcher(input);
    StringBuffer sb = new StringBuffer();
    while (m.find()) {
      MatchResult mr = m.toMatchResult();
      String rep = replacer.apply(mr);
      // Escape backslashes and dollars, as appendReplacement expects literal replacement with escapes
      rep = rep.replace("\\", "\\\\").replace("$", "\\$");
      m.appendReplacement(sb, rep);
    }
    m.appendTail(sb);
    return sb.toString();
  }

  // ---------- CSV (RFC4180-ish) ----------

  /** Convert fields to a CSV line; quote when needed. */
  public static String toCsvLine(List<String> fields) {
    if (fields == null || fields.isEmpty()) return "";
    StringJoiner sj = new StringJoiner(",");
    for (String f : fields) {
      String s = f == null ? "" : f;
      if (CSV_NEEDS_QUOTE.matcher(s).find()) {
        s = CSV_QUOTE.matcher(s).replaceAll("\"\"");
        s = "\"" + s + "\"";
      }
      sj.add(s);
    }
    return sj.toString();
  }

  /** Parse a single CSV line (no multi-line fields). */
  public static List<String> parseCsvLine(String line) {
    if (line == null) return Collections.emptyList();
    List<String> out = new ArrayList<String>();
    StringBuilder cur = new StringBuilder();
    boolean inQuotes = false;

    for (int i = 0; i < line.length(); i++) {
      char c = line.charAt(i);
      if (inQuotes) {
        if (c == '"') {
          if (i + 1 < line.length() && line.charAt(i + 1) == '"') {
            cur.append('"');
            i++;
          } else {
            inQuotes = false;
          }
        } else {
          cur.append(c);
        }
      } else {
        if (c == ',') {
          out.add(cur.toString());
          cur.setLength(0);
        } else if (c == '"') {
          inQuotes = true;
        } else {
          cur.append(c);
        }
      }
    }
    out.add(cur.toString());
    return out;
  }

  // ---------- Size Parsing / Formatting ----------

  private static final Map<String, Long> SIZE_SUFFIXES;
  static {
    Map<String, Long> m = new ConcurrentHashMap<String, Long>();
    m.put("b", 1L);
    m.put("kb", 1_000L);
    m.put("mb", 1_000_000L);
    m.put("gb", 1_000_000_000L);
    m.put("tb", 1_000_000_000_000L);
    m.put("kib", 1L << 10);
    m.put("mib", 1L << 20);
    m.put("gib", 1L << 30);
    m.put("tib", 1L << 40);
    SIZE_SUFFIXES = Collections.unmodifiableMap(m);
  }

  /** Parse human size like "10MB", "512KiB", "42b" (case-insensitive). */
  public static long parseSizeToBytes(String s) {
    if (isBlank(s)) throw new IllegalArgumentException("empty size");
    String t = s.trim().toLowerCase(Locale.ROOT);
    Matcher m = Pattern.compile("^([0-9]+)([a-zA-Z]+)?$").matcher(t);
    if (!m.find()) throw new IllegalArgumentException("Invalid size: " + s);
    long n = Long.parseLong(m.group(1));
    String suf = Optional.ofNullable(m.group(2)).orElse("b");
    Long mul = SIZE_SUFFIXES.get(suf);
    if (mul == null) throw new IllegalArgumentException("Unknown unit: " + suf);
    Long mul = SIZE_SUFFIXES.get(suf);
    if (mul == null) throw new IllegalArgumentException("Unknown unit: " + suf);
    // Check for overflow
    if (n > 0 && mul > Long.MAX_VALUE / n) {
        throw new IllegalArgumentException("Size overflow: " + s);
    }
    return Math.multiplyExact(n, mul);  // Java 8에서 사용 가능
}

  /** Format bytes into a human readable string with SI units by default. */
  public static String formatBytes(long bytes, boolean si) {
    final int unit = si ? 1000 : 1024;
    if (bytes < unit) return bytes + " B";
    int exp = (int) (Math.log(bytes) / Math.log(unit));
    String pre = (si ? "kMGTPE" : "KMGTPE").charAt(exp - 1) + (si ? "" : "i");
    return String.format(Locale.ROOT, "%.1f %sB", bytes / Math.pow(unit, exp), pre);
  }

  // ---------- Checksums / Hashing ----------

  /** Compute hex digest of given input stream using provided algorithm (e.g., "SHA-256"). */
  public static String checksum(InputStream in, String algorithm) throws IOException {
    Objects.requireNonNull(in, "in");
    Objects.requireNonNull(algorithm, "algorithm");
    try {
      MessageDigest md = MessageDigest.getInstance(algorithm);
      try (DigestInputStream dis = new DigestInputStream(new BufferedInputStream(in), md)) {
        byte[] buf = new byte[8192];
        while (dis.read(buf) != -1) { /* digest updates via stream */ }
      }
      return toHex(md.digest());
    } catch (NoSuchAlgorithmException e) {
      throw new IllegalArgumentException("Unknown algorithm: " + algorithm, e);
    }
  }

  /** Convenience: SHA-256 of text (UTF-8). */
  public static String sha256(String text) {
    if (text == null) text = "";
    try {
      MessageDigest md = MessageDigest.getInstance("SHA-256");
      byte[] bytes = md.digest(text.getBytes(DEFAULT_CHARSET));
      return toHex(bytes);
    } catch (NoSuchAlgorithmException e) {
      throw new RuntimeException(e);
    }
  }

  /** Convert bytes to hex string. */
  public static String toHex(byte[] bytes) {
    Formatter f = null;
    try {
      f = new Formatter(Locale.ROOT);
      for (byte b : bytes) f.format("%02x", b);
      return f.toString();
    } finally {
      if (f != null) f.close();
    }
  }

  // ---------- I/O Helpers ----------

  /**
   * Read all lines from a file with the given charset, but hard-limit the bytes to avoid OOM.
   * If the file exceeds the limit, only lines read before exceeding are returned.
   */
  public static List<String> readAllLinesWithLimit(Path path, Charset cs, long maxBytes) throws IOException {
    Objects.requireNonNull(path, "path");
    if (cs == null) cs = DEFAULT_CHARSET;
    if (maxBytes <= 0) throw new IllegalArgumentException("maxBytes must be > 0");
    long read = 0L;
    List<String> out = new ArrayList<String>();
    try (BufferedReader br = Files.newBufferedReader(path, cs)) {
      String line;
      while ((line = br.readLine()) != null) {
        read += line.getBytes(cs).length + 1;
        if (read > maxBytes) break;
        out.add(line);
      }
    }
    return out;
  }

  /**
   * Atomically write text to a file. Creates parent dirs if needed.
   * Uses a temp file then atomic move when supported by FS.
   */
  public static void writeTextAtomic(Path path, CharSequence content, Charset cs) throws IOException {
    Objects.requireNonNull(path, "path");
    if (cs == null) cs = DEFAULT_CHARSET;
    Files.createDirectories(path.getParent());
    Path tmp = path.resolveSibling(path.getFileName() + ".tmp-" + Instant.now().toEpochMilli());
    try (BufferedWriter bw = Files.newBufferedWriter(tmp, cs)) {
      bw.append(content == null ? "" : content);
    }
    try {
      Files.move(tmp, path, StandardCopyOption.ATOMIC_MOVE, StandardCopyOption.REPLACE_EXISTING);
    } catch (AtomicMoveNotSupportedException e) {
      Files.move(tmp, path, StandardCopyOption.REPLACE_EXISTING);
    }
  }

  // ---------- Tokenization / Parsing ----------

  /**
   * Split by delimiter but respect double quotes.
   * Example: a,"b,c",d  -> [a, b,c, d]
   */
  public static List<String> splitRespectingQuotes(String s, char delimiter) {
    if (s == null) return Collections.emptyList();
    List<String> out = new ArrayList<String>();
    StringBuilder cur = new StringBuilder();
    boolean inQuotes = false;
    for (int i = 0; i < s.length(); i++) {
      char c = s.charAt(i);
      if (c == '"') {
        inQuotes = !inQuotes;
      } else if (c == delimiter && !inQuotes) {
        out.add(cur.toString());
        cur.setLength(0);
      } else {
        cur.append(c);
      }
    }
    out.add(cur.toString());
    return out;
  }

  /**
   * Parse a semi-colon separated key=value string like "a=1;b=2;c=hello".
   * Keys are trimmed, empty keys ignored. Duplicate keys keep the last value.
   */
  public static Map<String, String> parseKeyValueList(String s) {
    if (isBlank(s)) return Collections.emptyMap();
    Map<String, String> out = new LinkedHashMap<String, String>();
    String[] parts = s.split(";");
    for (String part : parts) {
      int eq = part.indexOf('=');
      if (eq < 0) continue;
      String k = part.substring(0, eq).trim();
      if (k.isEmpty()) continue;
      String v = part.substring(eq + 1).trim();
      out.put(k, v);
    }
    return out;
  }

  /** Join map into "k=v" pairs sorted by key, joined with ';'. */
  public static String joinMapSorted(Map<String, String> m) {
    if (m == null || m.isEmpty()) return "";
    List<String> keys = new ArrayList<String>(m.keySet());
    Collections.sort(keys);
    StringJoiner sj = new StringJoiner(";");
    for (String k : keys) sj.add(k + "=" + m.get(k));
    return sj.toString();
  }

  // ---------- Algorithms ----------

  /** Levenshtein edit distance (iterative DP). O(n*m), O(min(n,m)) space. */
  public static int levenshtein(String a, String b) {
    if (Objects.equals(a, b)) return 0;
    if (a == null) return (b == null) ? 0 : b.length();
    if (b == null) return a.length();

    if (a.length() > b.length()) {
      String t = a; a = b; b = t;
    }
    int n = a.length();
    int m = b.length();
    int[] prev = new int[n + 1];
    int[] cur = new int[n + 1];
    for (int i = 0; i <= n; i++) prev[i] = i;
    for (int j = 1; j <= m; j++) {
      char bj = b.charAt(j - 1);
      cur[0] = j;
      for (int i = 1; i <= n; i++) {
        int cost = (a.charAt(i - 1) == bj) ? 0 : 1;
        cur[i] = Math.min(Math.min(cur[i - 1] + 1, prev[i] + 1), prev[i - 1] + cost);
      }
      int[] tmp = prev; prev = cur; cur = tmp;
    }
    return prev[n];
  }

  /** Longest Common Subsequence (LCS) length (O(n*m) time). */
  public static int lcsLength(String a, String b) {
    if (a == null || b == null) return 0;
    int n = a.length(), m = b.length();
    int[][] dp = new int[n + 1][m + 1];
    for (int i = 1; i <= n; i++) {
      char ca = a.charAt(i - 1);
      for (int j = 1; j <= m; j++) {
        char cb = b.charAt(j - 1);
        dp[i][j] = (ca == cb) ? dp[i - 1][j - 1] + 1
            : Math.max(dp[i - 1][j], dp[i][j - 1]);
      }
    }
    return dp[n][m];
  }

  /** Simple word diff summary: returns tokens unique to A, unique to B, and common. */
  public static DiffSummary wordDiff(String a, String b) {
    List<String> as = tokenizeWords(a);
    List<String> bs = tokenizeWords(b);
    List<String> onlyA = new ArrayList<String>(as);
    onlyA.removeAll(bs);
    List<String> onlyB = new ArrayList<String>(bs);
    onlyB.removeAll(as);
    List<String> common = new ArrayList<String>(as);
    common.retainAll(bs);
    return new DiffSummary(onlyA, onlyB, common);
  }

  private static List<String> tokenizeWords(String s) {
    if (isBlank(s)) return Collections.emptyList();
    return Arrays.asList(normalizeWhitespace(s).split(" "));
  }

  /** Java 8-compatible POJO for diff summary (instead of record). */
  public static final class DiffSummary {
    private final List<String> onlyA;
    private final List<String> onlyB;
    private final List<String> common;

    public DiffSummary(List<String> onlyA, List<String> onlyB, List<String> common) {
      this.onlyA = onlyA == null ? Collections.<String>emptyList() : Collections.unmodifiableList(onlyA);
      this.onlyB = onlyB == null ? Collections.<String>emptyList() : Collections.unmodifiableList(onlyB);
      this.common = common == null ? Collections.<String>emptyList() : Collections.unmodifiableList(common);
    }

    public List<String> getOnlyA() { return onlyA; }
    public List<String> getOnlyB() { return onlyB; }
    public List<String> getCommon() { return common; }

    @Override public String toString() {
      return "DiffSummary{onlyA=" + onlyA + ", onlyB=" + onlyB + ", common=" + common + "}";
    }
  }

  // ---------- Demo main ----------
  public static void main(String[] args) throws Exception {
    System.out.println(CLASS_NAME + " demo");
    System.out.println(slugify("안녕하세요, 세상! Hello, World! 2025", Locale.KOREA));
    System.out.println(truncateByCodePoints("emoji 😊 test", 8, "…"));
    System.out.println(toCsvLine(Arrays.asList("a", "b,c", "d\"e")));
    System.out.println(parseCsvLine("a,\"b,c\",\"d\"\"e\""));
    System.out.println(formatBytes(parseSizeToBytes("512KiB"), false));
    System.out.println("lev(kitten, sitting) = " + levenshtein("kitten", "sitting"));
    System.out.println("lcs(abcdef, acbcf) = " + lcsLength("abcdef", "acbcf"));
    System.out.println("valid slug? " + isValidSlugId("abc-123"));
    System.out.println(replaceAllFunc("a1b2", "\\d", new Function<MatchResult, String>() {
      @Override public String apply(MatchResult mr) { return "[" + mr.group() + "]"; }
    }));
  }

  // ---------- Validation Helper ----------

  /** Quick validator for a “slug-like” ID: lower-case letters, digits, hyphens, 1-64 chars. */
  public static boolean isValidSlugId(String s) {
    if (isBlank(s)) return false;
    if (s.length() < 1 || s.length() > 64) return false;
    return cachedPattern("^[a-z0-9-]+$").matcher(s).matches();
  }

  // ---------- Potential Review Topics (comments) ----------
  // TODO: 관심사 분리(Strings, Regex, Csv, Io, Math).
  // TODO: parseSizeToBytes overflow/negative checks.
  // TODO: readAllLinesWithLimit: 멀티바이트 인코딩에서 바이트 단위 정확도 개선.
  // TODO: RegexCache: 동시성·메모리 압력 지표/테스트 및 Caffeine 등 비교.
  // TODO: 슬러그 정책(한글 전사 옵션) 플래그화.
  // TODO: CSV 멀티라인 지원 추가.
  // TODO: lcsLength 공간 최적화.
}
