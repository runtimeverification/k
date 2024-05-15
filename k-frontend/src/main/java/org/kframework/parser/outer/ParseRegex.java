// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.outer;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import org.kframework.attributes.HasLocation;
import org.kframework.definition.regex.Regex;
import org.kframework.definition.regex.RegexBody;
import org.kframework.definition.regex.RegexSyntax;
import org.kframework.utils.errorsystem.KEMException;

public class ParseRegex {

  private static KEMException parseError(String msg, Scanner input, boolean reportIndex) {
    String base = "Syntax error";
    if (reportIndex) {
      base += " at index " + input.index();
    }
    base += " in regular expression";
    if (input.location().isPresent()) {
      return KEMException.innerParserError(base + ". " + msg, input.location().get());
    }
    return KEMException.innerParserError(base + ": \"" + input.contents() + "\". " + msg);
  }

  private static KEMException unescapedTokenError(int codePoint, Scanner input) {
    String strTok = Character.toString(codePoint);
    return parseError(
        "Unexpected token '" + strTok + "'. Did you mean '\\" + strTok + "'?", input, true);
  }

  private static class Scanner {
    private final String contents;
    private final int[] tokens;
    private int idx;
    private final Optional<HasLocation> loc;

    public Scanner(String input, HasLocation loc) {
      this(input, Optional.of(loc));
    }

    public Scanner(String input) {
      this(input, Optional.empty());
    }

    private Scanner(String input, Optional<HasLocation> loc) {
      this.contents = input;
      this.tokens = input.codePoints().toArray();
      this.idx = 0;
      this.loc = loc;
    }

    public Optional<HasLocation> location() {
      return loc;
    }

    public String contents() {
      return contents;
    }

    public int index() {
      return idx;
    }

    public boolean hasRemaining() {
      return idx != tokens.length;
    }

    public int peek() {
      return tokens[idx];
    }

    public int next() {
      if (!hasRemaining()) {
        throw new IndexOutOfBoundsException();
      }
      int res = tokens[idx];
      idx++;
      return res;
    }

    public boolean consume(int codePoint) {
      if (hasRemaining() && peek() == codePoint) {
        next();
        return true;
      }
      return false;
    }

    public void consumeOrError(int codePoint) {
      if (!hasRemaining()) {
        throw parseError(
            "Unexpected end of string. Expected '" + Character.toString(codePoint) + "'",
            this,
            false);
      }
      if (peek() != codePoint) {
        throw parseError(
            "Expected '"
                + Character.toString(codePoint)
                + "', but found '"
                + Character.toString(peek())
                + "'",
            this,
            true);
      }
      next();
    }

    public void back() {
      if (idx == 0) {
        throw new IndexOutOfBoundsException();
      }
      --idx;
    }
  }

  public static Regex parse(String regex, HasLocation loc) {
    return parse(new Scanner(regex, loc));
  }

  public static Regex parse(String regex) {
    return parse(new Scanner(regex));
  }

  public static RegexBody parseNamed(String regex, HasLocation loc) {
    return parseNamed(new Scanner(regex, loc));
  }

  public static RegexBody parseNamed(String regex) {
    return parseNamed(new Scanner(regex));
  }

  private static RegexBody parseNamed(Scanner input) {
    Regex reg = parse(input);
    if (reg.startLine() || reg.endLine()) {
      String msg = "Named lexical syntax cannot contain line anchors.";
      if (input.location().isPresent()) {
        throw KEMException.outerParserError(msg, input.location().get());
      }
      throw KEMException.outerParserError(msg);
    }
    return reg.reg();
  }

  private static Regex parse(Scanner input) {
    // A few special cases for better error messages
    String contents = input.contents();
    if (contents.isEmpty()) {
      throw parseError("Cannot be empty.", input, false);
    }
    if (contents.equals("^")) {
      throw parseError("Cannot consist of only line anchors. Did you mean '\\^'?", input, false);
    }
    if (contents.equals("$")) {
      throw parseError("Cannot consist of only line anchors. Did you mean '\\$'?", input, false);
    }
    if (contents.equals("^$")) {
      throw parseError(
          "Cannot consist of only line anchors. Did you mean '\\^' or '\\$'?", input, false);
    }

    boolean start = input.consume('^');
    RegexBody result = parseUnionExp(input);
    boolean end = input.consume('$');
    if (input.hasRemaining()) {
      input.back();
      throw unescapedTokenError('$', input);
    }
    return new Regex(start, result, end);
  }

  private static RegexBody parseUnionExp(Scanner input) {
    RegexBody concat = parseConcatExp(input);
    if (input.consume('|')) {
      if (!input.hasRemaining()) {
        input.back();
        throw unescapedTokenError('|', input);
      }
      return new RegexBody.Union(concat, parseUnionExp(input));
    }
    return concat;
  }

  private static RegexBody parseConcatExp(Scanner input) {
    List<RegexBody> members = new ArrayList<>();
    members.add(parseRepeatExp(input));
    while (input.hasRemaining()
        && input.peek() != ')'
        && input.peek() != '|'
        && input.peek() != '$') {
      members.add(parseRepeatExp(input));
    }
    if (members.size() == 1) {
      return members.get(0);
    }
    return new RegexBody.Concat(members);
  }

  private static RegexBody parseRepeatExp(Scanner input) {
    RegexBody result = parseCharClassExp(input);
    while (input.hasRemaining()) {
      int next = input.peek();
      if (next == '?') {
        input.next();
        result = new RegexBody.ZeroOrOneTimes(result);
      } else if (next == '*') {
        input.next();
        result = new RegexBody.ZeroOrMoreTimes(result);
      } else if (next == '+') {
        input.next();
        result = new RegexBody.OneOrMoreTimes(result);
      } else if (next == '{') {
        input.next();
        // Avoid conflict with {identifier}
        if (Character.isDigit(input.peek())) {
          result = parseRestOfTimesBraces(result, input);
        } else {
          input.back();
          break;
        }
      } else {
        break;
      }
    }
    return result;
  }

  private static RegexBody parseRestOfTimesBraces(RegexBody result, Scanner input) {
    int lower = parseInt(input);
    if (input.consume('}')) {
      return new RegexBody.ExactlyTimes(result, lower);
    }
    input.consumeOrError(',');
    if (input.consume('}')) {
      return new RegexBody.AtLeastTimes(result, lower);
    }
    int upper = parseInt(input);
    input.consumeOrError('}');
    return new RegexBody.RangeOfTimes(result, lower, upper);
  }

  private static int parseInt(Scanner input) {
    StringBuilder num = new StringBuilder();
    int peek = input.peek();
    while (Character.isDigit(peek)) {
      num.append(Character.toString(input.next()));
      peek = input.peek();
    }
    if (num.isEmpty()) {
      throw parseError(
          "Expected a digit 0-9, but found '" + Character.toString(peek) + "'.", input, true);
    }
    return Integer.parseInt(num.toString());
  }

  private static RegexBody parseCharClassExp(Scanner input) {
    if (!input.consume('[')) {
      return parseSimpleExp(input);
    }
    boolean negated = input.consume('^');
    List<RegexBody.CharClass> charClasses = new ArrayList<>();
    while (!input.consume(']')) {
      charClasses.add(parseCharClass(input));
    }
    if (charClasses.isEmpty()) {
      throw parseError("Character class cannot be empty.", input, true);
    }
    return new RegexBody.CharClassExp(negated, charClasses);
  }

  private static RegexBody.CharClass parseCharClass(Scanner input) {
    var chr1 = new RegexBody.CharClass.Char(parseCharExp(input, true));
    if (input.consume('-')) {
      if (input.consume(']')) {
        input.back();
        input.back();
        throw unescapedTokenError('-', input);
      }
      var chr2 = new RegexBody.CharClass.Char(parseCharExp(input, true));
      return new RegexBody.CharClass.Range(chr1, chr2);
    }
    return chr1;
  }

  private static int parseCharExp(Scanner input, boolean inCharClass) {
    if (input.consume('\\')) {
      int escape = input.next();
      return switch (escape) {
        case 'n' -> '\n';
        case 'r' -> '\r';
        case 't' -> '\t';
        default -> escape;
      };
    }
    int next = input.peek();
    if ((!inCharClass && RegexSyntax.K.reservedTokens.contains(next))
        || (inCharClass && RegexSyntax.K.reservedCharClassTokens.contains(next))) {
      throw unescapedTokenError(next, input);
    }
    return input.next();
  }

  private static RegexBody parseSimpleExp(Scanner input) {
    if (input.consume('.')) {
      return new RegexBody.AnyChar();
    }
    if (input.consume('(')) {
      RegexBody result = parseUnionExp(input);
      input.consumeOrError(')');
      return result;
    }
    if (input.consume('{')) {
      StringBuilder identifier = new StringBuilder();
      while (!input.consume('}')) {
        identifier.append(Character.toString(input.next()));
      }
      return new RegexBody.Named(Outer.parseSort(identifier.toString()).name());
    }
    return new RegexBody.Char(parseCharExp(input, false));
  }
}
