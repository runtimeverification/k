// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.definition.regex;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class RegexSyntax {
  private final Set<Integer> reservedTokens;
  private final Set<Integer> reservedCharClassTokens;

  private RegexSyntax(Set<Integer> reservedTokens, Set<Integer> reservedCharClassTokens) {
    this.reservedTokens = reservedTokens;
    this.reservedCharClassTokens = reservedCharClassTokens;
  }

  public String print(Regex reg) {
    return (reg.startLine() ? "^" : "") + printUnionExp(reg.reg()) + (reg.startLine() ? "$" : "");
  }

  public String printUnionExp(RegexBody reg) {
    if (reg instanceof RegexBody.Union un) {
      return printConcatExp(un.left()) + '|' + printConcatExp(un.right());
    }
    return printConcatExp(reg);
  }

  public String printConcatExp(RegexBody reg) {
    if (reg instanceof RegexBody.Concat con) {
      return con.members().stream().map(this::printRepeatExp).collect(Collectors.joining());
    }
    return printRepeatExp(reg);
  }

  public String printRepeatExp(RegexBody reg) {
    if (reg instanceof RegexBody.ZeroOrOneTimes question) {
      return printCharClassExp(question.reg()) + "?";
    }
    if (reg instanceof RegexBody.ZeroOrMoreTimes star) {
      return printCharClassExp(star.reg()) + "*";
    }
    if (reg instanceof RegexBody.OneOrMoreTimes plus) {
      return printCharClassExp(plus.reg()) + "+";
    }
    if (reg instanceof RegexBody.ExactlyTimes exact) {
      return printCharClassExp(exact.reg()) + "{" + exact.exactly() + "}";
    }
    if (reg instanceof RegexBody.AtLeastTimes atLeast) {
      return printCharClassExp(atLeast.reg()) + "{" + atLeast.atLeast() + ",}";
    }
    if (reg instanceof RegexBody.RangeOfTimes range) {
      return printCharClassExp(range.reg()) + "{" + range.atLeast() + "," + range.atMost() + "}";
    }
    return printCharClassExp(reg);
  }

  public String printCharClassExp(RegexBody reg) {
    if (reg instanceof RegexBody.CharClassExp clsExp) {
      return (clsExp.negated() ? "[^" : "[")
          + clsExp.charClasses().stream().map(this::printCharClass).collect(Collectors.joining())
          + "]";
    }
    return printSimpleExp(reg);
  }

  public String printCharClass(RegexBody.CharClass cls) {
    if (cls instanceof RegexBody.CharClass.Char chr) {
      return printChar(chr.codePoint(), reservedCharClassTokens);
    }
    if (cls instanceof RegexBody.CharClass.Range range) {
      return printChar(range.start(), reservedCharClassTokens)
          + "-"
          + printChar(range.end(), reservedCharClassTokens);
    }
    throw new AssertionError("Encountered unknown class " + cls.getClass().getName());
  }

  public String printSimpleExp(RegexBody reg) {
    if (reg instanceof RegexBody.Char chr) {
      return printChar(chr.codePoint(), reservedTokens);
    }
    if (reg instanceof RegexBody.AnyChar) {
      return ".";
    }
    if (reg instanceof RegexBody.Named name) {
      return "{" + name.name() + "}";
    }
    return "(" + printUnionExp(reg) + ")";
  }

  public String printChar(int codePoint, Set<Integer> reservedTokens) {
    return switch (codePoint) {
      case '\n' -> "\\n";
      case '\r' -> "\\r";
      case '\t' -> "\\t";
      default -> (reservedTokens.contains(codePoint) ? "\\" : "") + Character.toString(codePoint);
    };
  }

  private static Set<Integer> codePoints(Character... chars) {
    return Arrays.stream(chars).map(c -> (int) c).collect(Collectors.toSet());
  }

  public static final class K {
    private K() {}

    public static final Set<Integer> reservedTokens =
        codePoints('^', '$', '|', '?', '*', '+', '(', ')', '{', '}', '[', ']', '\\', '.', '"');
    public static final Set<Integer> reservedCharClassTokens = codePoints('^', '-', '\\', '[', ']');
    private static final RegexSyntax printer =
        new RegexSyntax(reservedTokens, reservedCharClassTokens);

    public static String print(Regex reg) {
      return printer.print(reg);
    }

    public static String print(RegexBody reg) {
      return printer.printUnionExp(reg);
    }

    public static String print(RegexBody.CharClass cls) {
      return printer.printCharClass(cls);
    }
  }

  public static final class Flex {
    private Flex() {}

    public static final Set<Integer> reservedTokens =
        Stream.concat(K.reservedTokens.stream(), codePoints('/', '<', '>', ' ').stream())
            .collect(Collectors.toSet());
    public static final Set<Integer> reservedCharClassTokens =
        Stream.concat(K.reservedCharClassTokens.stream(), codePoints(' ').stream())
            .collect(Collectors.toSet());
    private static final RegexSyntax printer =
        new RegexSyntax(reservedTokens, reservedCharClassTokens) {
          // Parenthesize non-ASCII codepoints because Flex treats them as a sequence of bytes
          // rather than a single character
          @Override
          public String printChar(int codePoint, Set<Integer> reservedTokens) {
            String res = super.printChar(codePoint, reservedTokens);
            if (codePoint > 127) {
              res = '(' + res + ')';
            }
            return res;
          }
        };

    /** Convert a K lexical identifier to a Flex-compatible one */
    public static String mangleIdentifier(String name) {
      // K identifiers match "#?[A-Z][a-zA-Z0-9]*"
      // Flex identifiers match "[_a-zA-Z][a-zA-Z0-9_\-]*"
      if (name.startsWith("#")) {
        return "_Hash_" + name.substring(1);
      }
      return name;
    }

    private static final RegexTransformer convert =
        new RegexTransformer() {
          // Make identifiers Flex-compatible
          @Override
          public RegexBody apply(RegexBody.Named named) {
            return new RegexBody.Named(mangleIdentifier(named.name()));
          }

          // Factor non-ASCII characters out of character classes into an explicit |,
          // lest Flex treat each byte as its own character in the class.
          @Override
          public RegexBody apply(RegexBody.CharClassExp clsExp) {
            // non-ASCII is unsupported in negated character classes
            if (clsExp.negated()) {
              return super.apply(clsExp);
            }

            List<RegexBody> factors = new ArrayList<>();
            List<RegexBody.CharClass> keepIn = new ArrayList<>();
            for (RegexBody.CharClass cls : clsExp.charClasses()) {
              if (cls instanceof RegexBody.CharClass.Char chr && chr.codePoint() > 127) {
                factors.add(new RegexBody.Char(chr.codePoint()));
              } else {
                keepIn.add(cls);
              }
            }
            if (!keepIn.isEmpty()) {
              factors.add(new RegexBody.CharClassExp(false, keepIn));
            }
            RegexBody result = factors.get(0);
            for (RegexBody factor : factors.subList(1, factors.size())) {
              result = new RegexBody.Union(result, factor);
            }
            return result;
          }
        };

    public static String print(Regex reg) {
      return printer.print(convert.apply(reg));
    }

    public static String print(RegexBody reg) {
      return printer.printUnionExp(convert.apply(reg));
    }

    public static String print(RegexBody.CharClass cls) {
      return printer.printCharClass(convert.apply(cls));
    }
  }
}
