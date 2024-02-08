// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils;

import java.util.HashMap;
import java.util.Map;
import java.util.regex.Pattern;

public class StringUtil {
  /**
   * Unescape the textual representation of a string specific to SDF and Maude. It removes the
   * double quote at the beginning and end, and transforms special sequence of characters like "\n"
   * into the newline character.
   */
  public static String unquoteCString(String str) {
    return unquoteCString(str, '"');
  }

  public static String unquoteCString(String str, char delimiter) {
    StringBuilder sb = new StringBuilder();
    if (str.charAt(0) != delimiter) {
      throw new IllegalArgumentException(
          "Expected to find " + delimiter + " at the beginning of string: " + str);
    }
    if (str.charAt(str.length() - 1) != delimiter) {
      throw new IllegalArgumentException(
          "Expected to find " + delimiter + " at the end of string: " + str);
    }
    for (int i = 1; i < str.length() - 1; i++) {
      if (str.charAt(i) == '\\') {
        if (str.charAt(i + 1) == '\\') sb.append('\\');
        else if (str.charAt(i + 1) == 'n') sb.append('\n');
        else if (str.charAt(i + 1) == 'r') sb.append('\r');
        else if (str.charAt(i + 1) == 't') sb.append('\t');
        else if (str.charAt(i + 1) == 'f') sb.append('\f');
        else if (str.charAt(i + 1) == delimiter) sb.append(delimiter);
        else if (str.charAt(i + 1) >= '0' && str.charAt(i + 1) <= '9') {
          // found an octal value
          int a2 = str.charAt(i + 1) - '0';
          int a1 = str.charAt(i + 2) - '0';
          if (a1 < 0 || a1 > 9)
            throw new IllegalArgumentException("Malformed octal value in string:" + str);
          int a0 = str.charAt(i + 3) - '0';
          if (a0 < 0 || a0 > 9)
            throw new IllegalArgumentException("Malformed octal value in string:" + str);
          int decimal = a2 * 8 * 8 + a1 * 8 + a0;
          sb.append((char) decimal);
          i++;
          i++;
        }
        i++;
      } else sb.append(str.charAt(i));
    }

    return sb.toString();
  }

  /**
   * Takes the internal representation of a string, and creates the textual representation that is
   * ready to be printed. It adds double quote at the beginning and end, and transforms special
   * characters into the textual representation (ex: newline becomes "\n").
   */
  public static String enquoteCString(String value) {
    return enquoteCString(value, '"');
  }

  public static String enquoteCString(String value, char delimiter) {
    final int length = value.length();
    StringBuilder result = new StringBuilder();
    result.append(delimiter);
    for (int offset = 0, codepoint; offset < length; offset += Character.charCount(codepoint)) {
      codepoint = value.codePointAt(offset);
      if (codepoint > 0xFF) {
        result.appendCodePoint(codepoint);
      } else if (codepoint == delimiter) {
        result.append("\\" + delimiter);
      } else if (codepoint == '\\') {
        result.append("\\\\");
      } else if (codepoint == '\n') {
        result.append("\\n");
      } else if (codepoint == '\t') {
        result.append("\\t");
      } else if (codepoint == '\r') {
        result.append("\\r");
      } else if (codepoint == '\f') {
        result.append("\\f");
      } else if (codepoint >= 32 && codepoint < 127) {
        result.append((char) codepoint);
      } else if (codepoint <= 0xff) {
        result.append("\\");
        result.append(String.format("%03o", codepoint));
      }
    }
    result.append(delimiter);
    return result.toString();
  }

  public static void throwIfSurrogatePair(int codePoint) {
    if (codePoint >= 0xd800 && codePoint <= 0xdfff) {
      // we are trying to encode a surrogate pair, which the unicode
      // standard forbids
      throw new IllegalArgumentException(
          Integer.toHexString(codePoint) + " is not in the accepted unicode range.");
    }
    if (codePoint >= 0x110000)
      throw new IllegalArgumentException(
          Integer.toHexString(codePoint) + " is not in the accepted unicode range.");
  }

  public static int lastIndexOfAny(String str, String search, int offset) {
    if (str.equals("") || search.equals("")) {
      return -1;
    }
    int start = str.offsetByCodePoints(0, offset);
    for (int i = start, strCodepoint; i >= 0; i -= Character.charCount(strCodepoint)) {
      strCodepoint = str.codePointAt(i);
      for (int j = search.length() - 1, searchCodepoint;
          j >= 0;
          j -= Character.charCount(searchCodepoint)) {
        searchCodepoint = search.codePointAt(j);
        if (strCodepoint == searchCodepoint) {
          return i;
        }
      }
    }
    return -1;
  }

  public static int indexOfAny(String str, String search, int offset) {
    if (str.equals("") || search.equals("")) {
      return -1;
    }
    int start = str.offsetByCodePoints(0, offset);
    for (int i = start, strCodepoint; i < str.length(); i += Character.charCount(strCodepoint)) {
      strCodepoint = str.codePointAt(i);
      for (int j = 0, searchCodepoint;
          j < search.length();
          j += Character.charCount(searchCodepoint)) {
        searchCodepoint = search.codePointAt(j);
        if (strCodepoint == searchCodepoint) {
          return i;
        }
      }
    }
    return -1;
  }

  /**
   * Removes the first and last double-quote characters and unescapes special characters that start
   * with backslash: newline, carriage return, line feed, tab and backslash. Characters between 127
   * and 255 are stored as \xFF Characters between 256 and 65535 are stored as \uFFFF Characters
   * above 65536 are stored as \u0010FFFF
   *
   * @param str Python like double-quoted string
   * @return unescaped and unquoted string
   */
  public static String unquoteKString(String str) {
    StringBuilder sb = new StringBuilder();
    if (str.charAt(0) != '"') {
      throw new IllegalArgumentException(
          "Expected to find double quote at the beginning of string: " + str);
    }
    if (str.charAt(str.length() - 1) != '"') {
      throw new IllegalArgumentException(
          "Expected to find double quote at the end of string: " + str);
    }
    for (int i = 1; i < str.length() - 1; i++) {
      if (str.charAt(i) == '\\') {
        if (str.charAt(i + 1) == '"') {
          sb.append('"');
          i++;
        } else if (str.charAt(i + 1) == '\\') {
          sb.append('\\');
          i++;
        } else if (str.charAt(i + 1) == 'n') {
          sb.append('\n');
          i++;
        } else if (str.charAt(i + 1) == 'r') {
          sb.append('\r');
          i++;
        } else if (str.charAt(i + 1) == 't') {
          sb.append('\t');
          i++;
        } else if (str.charAt(i + 1) == 'f') {
          sb.append('\f');
          i++;
        } else if (str.charAt(i + 1) == 'x') {
          String arg = str.substring(i + 2, i + 4);
          sb.append((char) Integer.parseInt(arg, 16));
          i += 3;
        } else if (str.charAt(i + 1) == 'u') {
          String arg = str.substring(i + 2, i + 6);
          int codePoint = Integer.parseInt(arg, 16);
          StringUtil.throwIfSurrogatePair(codePoint);
          sb.append((char) codePoint);
          i += 5;
        } else if (str.charAt(i + 1) == 'U') {
          String arg = str.substring(i + 2, i + 10);
          int codePoint = Integer.parseInt(arg, 16);
          StringUtil.throwIfSurrogatePair(codePoint);
          sb.append(Character.toChars(codePoint));
          i += 9;
        }
      } else {
        sb.append(str.charAt(i));
      }
    }
    return sb.toString();
  }

  /**
   * Get the escaped string for a Unicode codepoint: Codepoints between 32 and 126 are stored
   * directly as the character Codepoints between 0 and 31 and between 127 and 255 are stored as
   * \xFF Codepoints between 256 and 65535 are stored as \uFFFF Codepoints above 65536 are stored as
   * \u0010FFFF
   *
   * @param codepoint a Unicode codepoint
   * @return representation of the codepoint as an escaped string
   */
  public static String getUnicodeEscape(int codepoint) {
    if (32 <= codepoint && codepoint < 127) {
      return String.valueOf((char) codepoint);
    }
    if (codepoint <= 0xff) {
      return "\\x" + String.format("%02x", codepoint);
    }
    if (codepoint <= 0xffff) {
      return "\\u" + String.format("%04x", codepoint);
    }
    return "\\U" + String.format("%08x", codepoint);
  }

  /**
   * Adds double-quote at the beginning and end of the string and escapes special characters with
   * backslash: newline, carriage return, line feed, tab and backslash. Characters between 127 and
   * 255 are stored as \xFF Characters between 256 and 65535 are stored as \uFFFF Characters above
   * 65536 are stored as \u0010FFFF
   *
   * @param value any string
   * @return Python like textual representation of the string
   */
  public static String enquoteKString(String value) {
    final int length = value.length();
    StringBuilder result = new StringBuilder();
    result.append("\"");
    for (int offset = 0, codepoint; offset < length; offset += Character.charCount(codepoint)) {
      codepoint = value.codePointAt(offset);
      if (codepoint == '"') {
        result.append("\\\"");
      } else if (codepoint == '\\') {
        result.append("\\\\");
      } else if (codepoint == '\n') {
        result.append("\\n");
      } else if (codepoint == '\t') {
        result.append("\\t");
      } else if (codepoint == '\r') {
        result.append("\\r");
      } else if (codepoint == '\f') {
        result.append("\\f");
      } else {
        result.append(StringUtil.getUnicodeEscape(codepoint));
      }
    }
    result.append("\"");
    return result.toString();
  }

  /**
   * Escapes all non-ASCII characters as follows: Characters between 32 and 126 are stored directly
   * as the character Characters between 0 and 31 and between 127 and 255 are stored as \xFF
   * Characters between 256 and 65535 are stored as \uFFFF Characters above 65536 are stored as
   * \u0010FFFF
   *
   * @param value any string
   * @return representation of the string with non-ASCII characters escaped
   */
  public static String escapeNonASCII(String value) {
    final int length = value.length();
    StringBuilder result = new StringBuilder();
    for (int offset = 0, codepoint; offset < length; offset += Character.charCount(codepoint)) {
      codepoint = value.codePointAt(offset);
      result.append(StringUtil.getUnicodeEscape(codepoint));
    }
    return result.toString();
  }

  /**
   * split string to lines in a way that no lines will exceed 80 columns NOTE: strings split only at
   * whitespace character ' ', if string contains no ' ', it's returned as is
   *
   * @param str string to split
   * @return new string with newlines added
   */
  public static String splitLines(String str) {
    return splitLines(str, 80);
  }

  /**
   * split string to lines in a way that no lines will exceed `col` columns NOTE: strings split only
   * at whitespace character ' ', if string contains no ' ', it's returned as is
   *
   * @param str string to split
   * @param col rightmost column
   * @return new string with newlines added
   */
  public static String splitLines(String str, final int col) {
    String[] lines = str.split("\n");
    StringBuilder builder = new StringBuilder();
    String nl = "";
    for (String line : lines) {
      builder.append(nl);
      if (line.length() < col) {
        builder.append(line);
      } else {
        builder.append(splitLine(line, col));
      }
      nl = "\n";
    }
    return builder.toString();
  }

  private static String splitLine(String str, final int col) {
    if (str.length() < col) {
      return str;
    }

    // keep indentation of long lines (like term ambiguities)
    int firstChar = 0;
    while (str.charAt(firstChar) == ' ') firstChar++;
    // scan from `col` to left
    for (int i = col - 1; i > firstChar; i--) {
      if (str.charAt(i) == ' ') {
        return str.substring(0, i) + "\n" + splitLine(str.substring(i + 1), col);
      }
    }

    // we reached the beginning of the string and it contains no whitespaces before the `col`
    // but it's longer than `col` so we should replace first space after rightmost column
    // with a newline to make it shorter
    for (int i = col; i < str.length(); i++) {
      if (str.charAt(i) == ' ') {
        return str.substring(0, i) + "\n" + splitLine(str.substring(i + 1), col);
      }
    }

    // string has no spaces to split
    return str;
  }

  /**
   * Takes a textual representation of a KLabel using backticks to delimit and returns the string
   * representation of the KLabel that it corresponds to
   *
   * <p>Used by the KAST parser.
   *
   * @param str An image of a parser token corresponding to a KLabel in KORE which begins and ends
   *     with backtick
   * @return The string value of the KLabel
   */
  public static String unescapeKoreKLabel(String str) {
    char delimiter = '`';
    StringBuilder sb = new StringBuilder();
    if (str.charAt(0) != delimiter) {
      throw new IllegalArgumentException(
          "Expected to find " + delimiter + " at the beginning of string: " + str);
    }
    if (str.charAt(str.length() - 1) != delimiter) {
      throw new IllegalArgumentException(
          "Expected to find " + delimiter + " at the end of string: " + str);
    }
    for (int i = 1; i < str.length() - 1; i++) {
      if (str.charAt(i) == 0x7F || str.charAt(i) < 32)
        throw new IllegalArgumentException("Special characters not supported here:" + str);
      if (str.charAt(i) == '\\') {
        if (str.charAt(i + 1) == '\\') sb.append('\\');
        else if (str.charAt(i + 1) == delimiter) sb.append(delimiter);
        i++;
      } else sb.append(str.charAt(i));
    }

    return sb.toString();
  }

  public static String[] asciiReadableEncodingDefault =
      new String[] {
        null, // 00
        null, // 01
        null, // 02
        null, // 03
        null, // 04
        null, // 05
        null, // 06
        null, // 07
        null, // 08
        null, // 09
        null, // 0a
        null, // 0b
        null, // 0c
        null, // 0d
        null, // 0e
        null, // 0f
        null, // 10
        null, // 11
        null, // 12
        null, // 13
        null, // 14
        null, // 15
        null, // 16
        null, // 17
        null, // 18
        null, // 19
        null, // 1a
        null, // 1b
        null, // 1c
        null, // 1d
        null, // 1e
        null, // 1f
        "Spce", // 20
        "Bang", // 21
        "Quot", // 22
        "Hash", // 23
        "Dolr", // 24
        "Perc", // 25
        "And", // 26
        "Apos", // 27
        "LPar", // 28
        "RPar", // 29
        "Star", // 2a
        "Plus", // 2b
        "Comm", // 2c
        "-", // 2d
        "Stop", // 2e
        "Slsh", // 2f
        "0", // 30
        "1", // 31
        "2", // 32
        "3", // 33
        "4", // 34
        "5", // 35
        "6", // 36
        "7", // 37
        "8", // 38
        "9", // 39
        "Coln", // 3a
        "SCln", // 3b
        "LT", // 3c
        "Eqls", // 3d
        "GT", // 3e
        "Ques", // 3f
        "AT", // 40
        "A", // 41
        "B", // 42
        "C", // 43
        "D", // 44
        "E", // 45
        "F", // 46
        "G", // 47
        "H", // 48
        "I", // 49
        "J", // 4a
        "K", // 4b
        "L", // 4c
        "M", // 4d
        "N", // 4e
        "O", // 4f
        "P", // 50
        "Q", // 51
        "R", // 52
        "S", // 53
        "T", // 54
        "U", // 55
        "V", // 56
        "W", // 57
        "X", // 58
        "Y", // 59
        "Z", // 5a
        "LSqB", // 5b
        "Bash", // 5c
        "RSqB", // 5d
        "Xor", // 5e
        "Unds", // 5f
        "BQuo", // 60
        "a", // 61
        "b", // 62
        "c", // 63
        "d", // 64
        "e", // 65
        "f", // 66
        "g", // 67
        "h", // 68
        "i", // 69
        "j", // 6a
        "k", // 6b
        "l", // 6c
        "m", // 6d
        "n", // 6e
        "o", // 6f
        "p", // 70
        "q", // 71
        "r", // 72
        "s", // 73
        "t", // 74
        "u", // 75
        "v", // 76
        "w", // 77
        "x", // 78
        "y", // 79
        "z", // 7a
        "LBra", // 7b
        "Pipe", // 7c
        "RBra", // 7d
        "Tild", // 7e
        null // 7f
      };
  private static final Map<String, Character> asciiReadableEncodingDefaultMap = new HashMap<>();

  static {
    for (int i = 0; i < asciiReadableEncodingDefault.length; i++)
      if (asciiReadableEncodingDefault[i] != null && asciiReadableEncodingDefault[i].length() > 1)
        asciiReadableEncodingDefaultMap.put(asciiReadableEncodingDefault[i], (char) i);
  }

  /**
   * Encode special characters depending on context.
   *
   * @param asciiReadableEncodingTable Override the default `asciiReadableEncodingDefault` depending
   *     on language requirements
   * @param identChar which characters to replace
   */
  public static void encodeStringToAlphanumeric(
      StringBuilder sb,
      String name,
      String[] asciiReadableEncodingTable,
      Pattern identChar,
      String escapeChar) {
    boolean inIdent = true;
    for (int i = 0; i < name.length(); i++) {
      if (identChar.matcher(name).region(i, name.length()).lookingAt()) {
        if (!inIdent) {
          inIdent = true;
          sb.append(escapeChar);
        }
        sb.append(name.charAt(i));
      } else {
        if (inIdent) {
          inIdent = false;
          sb.append(escapeChar);
        }
        int charAt = name.charAt(i);
        if (charAt < 128 && asciiReadableEncodingTable[charAt] != null) {
          sb.append(asciiReadableEncodingTable[charAt]);
        } else {
          sb.append(String.format("%04x", charAt));
        }
      }
    }
    if (!inIdent) {
      sb.append("'");
    }
  }

  public static String decodeKoreString(String encoded) {
    boolean quotedState = false;
    StringBuilder resultedEncoding = new StringBuilder();
    for (int i = 0; i < encoded.length(); i++) {
      if (quotedState) {
        if (encoded.charAt(i) == '\'') {
          quotedState = false;
        } else {
          resultedEncoding.append(asciiReadableEncodingDefaultMap.get(encoded.substring(i, i + 4)));
          i += 3;
        }
      } else {
        if (encoded.charAt(i) == '\'') {
          quotedState = true;
        } else resultedEncoding.append(encoded.charAt(i));
      }
    }
    return resultedEncoding.toString();
  }

  public static String[] splitOneDimensionalAtt(String att) {
    String[] splitted = att.trim().split(",");
    for (int i = 0; i < splitted.length; i++) {
      splitted[i] = splitted[i].trim();
    }
    return splitted;
  }

  public static String[][] splitTwoDimensionalAtt(String att) {
    String[] parts = att.trim().split(";");
    String[][] splitted = new String[parts.length][];
    for (int i = 0; i < parts.length; i++) {
      String[] subparts = splitOneDimensionalAtt(parts[i]);
      splitted[i] = subparts;
    }
    return splitted;
  }
}
