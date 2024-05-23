// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.definition.regex;

import java.util.stream.Stream;

public class RegexTransformer {
  public Regex apply(Regex reg) {
    return new Regex(reg.startLine(), apply(reg.reg()), reg.endLine());
  }

  public RegexBody apply(RegexBody reg) {
    if (reg instanceof RegexBody.Char chr) {
      return apply(chr);
    }
    if (reg instanceof RegexBody.AnyChar dot) {
      return apply(dot);
    }
    if (reg instanceof RegexBody.Named named) {
      return apply(named);
    }
    if (reg instanceof RegexBody.CharClassExp cls) {
      return apply(cls);
    }
    if (reg instanceof RegexBody.Union un) {
      return apply(un);
    }
    if (reg instanceof RegexBody.Concat con) {
      return apply(con);
    }
    if (reg instanceof RegexBody.ZeroOrMoreTimes star) {
      return apply(star);
    }
    if (reg instanceof RegexBody.ZeroOrOneTimes question) {
      return apply(question);
    }
    if (reg instanceof RegexBody.OneOrMoreTimes plus) {
      return apply(plus);
    }
    if (reg instanceof RegexBody.ExactlyTimes exact) {
      return apply(exact);
    }
    if (reg instanceof RegexBody.AtLeastTimes atLeast) {
      return apply(atLeast);
    }
    if (reg instanceof RegexBody.RangeOfTimes range) {
      return apply(range);
    }
    throw new AssertionError("Unhandled class in RegexTransformer: " + reg.getClass());
  }

  public RegexBody apply(RegexBody.Char chr) {
    return new RegexBody.Char(chr.codePoint());
  }

  public RegexBody apply(RegexBody.AnyChar dot) {
    return new RegexBody.AnyChar();
  }

  public RegexBody apply(RegexBody.Named named) {
    return new RegexBody.Named(named.name());
  }

  public RegexBody apply(RegexBody.CharClassExp cls) {
    return new RegexBody.CharClassExp(
        cls.negated(), cls.charClasses().stream().map(this::apply).toList());
  }

  public RegexBody.CharClass apply(RegexBody.CharClass cls) {
    if (cls instanceof RegexBody.CharClass.Char chr) {
      return apply(chr);
    }
    if (cls instanceof RegexBody.CharClass.Range range) {
      return apply(range);
    }
    throw new AssertionError("Unhandled class in RegexTransformer: " + cls.getClass());
  }

  public RegexBody.CharClass apply(RegexBody.CharClass.Char chr) {
    return new RegexBody.CharClass.Char(chr.codePoint());
  }

  public RegexBody.CharClass apply(RegexBody.CharClass.Range range) {
    return new RegexBody.CharClass.Range(range.start(), range.end());
  }

  public RegexBody apply(RegexBody.Union un) {
    return new RegexBody.Union(apply(un.left()), apply(un.right()));
  }

  public RegexBody apply(RegexBody.Concat con) {
    return new RegexBody.Concat(
        con.members().stream()
            .map(this::apply)
            .flatMap(
                m -> m instanceof RegexBody.Concat mCon ? mCon.members().stream() : Stream.of(m))
            .toList());
  }

  public RegexBody apply(RegexBody.ZeroOrMoreTimes star) {
    return new RegexBody.ZeroOrMoreTimes(apply(star.reg()));
  }

  public RegexBody apply(RegexBody.ZeroOrOneTimes question) {
    return new RegexBody.ZeroOrOneTimes(apply(question.reg()));
  }

  public RegexBody apply(RegexBody.OneOrMoreTimes plus) {
    return new RegexBody.OneOrMoreTimes(apply(plus.reg()));
  }

  public RegexBody apply(RegexBody.ExactlyTimes exact) {
    return new RegexBody.ExactlyTimes(apply(exact.reg()), exact.exactly());
  }

  public RegexBody apply(RegexBody.AtLeastTimes atLeast) {
    return new RegexBody.AtLeastTimes(apply(atLeast.reg()), atLeast.atLeast());
  }

  public RegexBody apply(RegexBody.RangeOfTimes range) {
    return new RegexBody.RangeOfTimes(apply(range.reg()), range.atLeast(), range.atMost());
  }
}
