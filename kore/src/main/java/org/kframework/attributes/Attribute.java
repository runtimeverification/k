// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.attributes;

import com.google.common.collect.Sets;
import java.util.Arrays;
import java.util.EnumSet;

public abstract class Attribute {

  public enum Syntax {
    CELL,
    CLAIM,
    CONTEXT,
    CONTEXT_ALIAS,
    MODULE,
    PRODUCTION,
    RULE,
    SENTENCE,
    SYNTAX_SORT,
    UNCHECKED
  }

  public sealed interface Visibility {
    record User(EnumSet<Syntax> allowedSyntax) implements Visibility {
      User(Syntax... allowed) {
        this(Sets.newEnumSet(Arrays.asList(allowed), Syntax.class));
      }
    }

    record Internal() implements Visibility {}
  }

  public enum EmitToKORE {
    YES,
    NO
  }

  public final Visibility visibility;
  public final EmitToKORE emit;

  protected Attribute(Visibility visibility, EmitToKORE emit) {
    this.visibility = visibility;
    this.emit = emit;
  }
}
