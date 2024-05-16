// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.definition.regex;

import java.io.Serializable;

public record Regex(boolean startLine, RegexBody reg, boolean endLine) implements Serializable {
  public Regex(RegexBody reg) {
    this(false, reg, false);
  }
}
