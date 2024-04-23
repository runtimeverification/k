// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner.disambiguation.inference;

import java.util.HashSet;
import java.util.Set;
import org.kframework.kore.SortHead;

/** An unsimplified sort analogous to SimpleSub's SimpleType. */
public sealed interface BoundedSort {
  /** A primitive sort */
  record Constructor(SortHead head) implements BoundedSort {}

  /**
   * A sort variable with sub- and super-type constraints.
   *
   * @param sortVar - The underlying SortVariable. This holds no real information, but is needed to
   *     prevent distinct Variables with the same bounds from comparing equal.
   * @param lowerBounds - All those sorts which must be a sub-type of this variable
   * @param upperBounds - All those sorts which must be a super-type of this variable
   */
  record Variable(SortVariable sortVar, Set<BoundedSort> lowerBounds, Set<BoundedSort> upperBounds)
      implements BoundedSort {

    Variable() {
      this(new SortVariable(), new HashSet<>(), new HashSet<>());
    }
  }
}
