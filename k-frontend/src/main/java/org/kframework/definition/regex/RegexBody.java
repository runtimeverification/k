// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.definition.regex;

import java.io.Serializable;
import java.util.List;

public sealed interface RegexBody extends Serializable {
  record Char(int codePoint) implements RegexBody {}

  record AnyChar() implements RegexBody {}

  record Named(String name) implements RegexBody {}

  record CharClassExp(boolean negated, List<CharClass> charClasses) implements RegexBody {}

  sealed interface CharClass extends Serializable {
    record Char(int codePoint) implements CharClass {}

    record Range(int start, int end) implements CharClass {}
  }

  record Union(RegexBody left, RegexBody right) implements RegexBody {}

  record Concat(List<RegexBody> members) implements RegexBody {}

  record ZeroOrMoreTimes(RegexBody reg) implements RegexBody {}

  record ZeroOrOneTimes(RegexBody reg) implements RegexBody {}

  record OneOrMoreTimes(RegexBody reg) implements RegexBody {}

  record ExactlyTimes(RegexBody reg, int exactly) implements RegexBody {}

  record AtLeastTimes(RegexBody reg, int atLeast) implements RegexBody {}

  record RangeOfTimes(RegexBody reg, int atLeast, int atMost) implements RegexBody {}
}
