// Copyright (c) K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation.inference;

import java.util.ArrayList;
import java.util.List;
import org.kframework.kore.SortHead;

public sealed interface BoundedSort {
  record Constructor(SortHead head) implements BoundedSort {}

  // This is a class rather than a record because we want reference equality
  final class Variable implements BoundedSort {
    private final SortVariable sortVar = new SortVariable();
    private final List<BoundedSort> lowerBounds = new ArrayList<>();
    private final List<BoundedSort> upperBounds = new ArrayList<>();

    public Variable() {}

    public SortVariable sortVar() {
      return sortVar;
    }

    public List<BoundedSort> lowerBounds() {
      return lowerBounds;
    }

    public List<BoundedSort> upperBounds() {
      return upperBounds;
    }
  }
}
