// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.definition.regex;

public class RegexVisitor {
  public void apply(Regex reg) {
    apply(reg.reg());
  }

  public void apply(RegexBody reg) {
    if (reg instanceof RegexBody.Char chr) {
      apply(chr);
    } else if (reg instanceof RegexBody.AnyChar dot) {
      apply(dot);
    } else if (reg instanceof RegexBody.Named named) {
      apply(named);
    } else if (reg instanceof RegexBody.CharClassExp cls) {
      apply(cls);
    } else if (reg instanceof RegexBody.Union un) {
      apply(un);
    } else if (reg instanceof RegexBody.Concat con) {
      apply(con);
    } else if (reg instanceof RegexBody.ZeroOrMoreTimes star) {
      apply(star);
    } else if (reg instanceof RegexBody.ZeroOrOneTimes question) {
      apply(question);
    } else if (reg instanceof RegexBody.OneOrMoreTimes plus) {
      apply(plus);
    } else if (reg instanceof RegexBody.ExactlyTimes exact) {
      apply(exact);
    } else if (reg instanceof RegexBody.AtLeastTimes atLeast) {
      apply(atLeast);
    } else if (reg instanceof RegexBody.RangeOfTimes range) {
      apply(range);
    } else {
      throw new AssertionError("Unhandled class in RegexVisitor: " + reg.getClass());
    }
  }

  public void apply(RegexBody.Char chr) {}

  public void apply(RegexBody.AnyChar dot) {}

  public void apply(RegexBody.Named named) {}

  public void apply(RegexBody.CharClassExp cls) {
    cls.charClasses().forEach(this::apply);
  }

  public void apply(RegexBody.CharClass cls) {
    if (cls instanceof RegexBody.CharClass.Char chr) {
      apply(chr);
    } else if (cls instanceof RegexBody.CharClass.Range range) {
      apply(range);
    } else {
      throw new AssertionError("Unhandled class in RegexVisitor: " + cls.getClass());
    }
  }

  public void apply(RegexBody.CharClass.Char chr) {}

  public void apply(RegexBody.CharClass.Range range) {}

  public void apply(RegexBody.Union un) {
    apply(un.left());
    apply(un.right());
  }

  public void apply(RegexBody.Concat con) {
    con.members().forEach(this::apply);
  }

  public void apply(RegexBody.ZeroOrMoreTimes star) {
    apply(star.reg());
  }

  public void apply(RegexBody.ZeroOrOneTimes question) {
    apply(question.reg());
  }

  public void apply(RegexBody.OneOrMoreTimes plus) {
    apply(plus.reg());
  }

  public void apply(RegexBody.ExactlyTimes exact) {
    apply(exact.reg());
  }

  public void apply(RegexBody.AtLeastTimes atLeast) {
    apply(atLeast.reg());
  }

  public void apply(RegexBody.RangeOfTimes range) {
    apply(range.reg());
  }
}
