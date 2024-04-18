// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner.disambiguation.inference;

/**
 * A variable which could be instantiated with any Sort.
 *
 * <p>This class is necessary to ensure that all distinct variable instances compare unequal. In
 * particular, we can't just use {@code Sort("X")} to represent a sort variable lest {@code new
 * Sort("X").equals(new Sort("X"))} even when the {@code X} arises from two different
 * ProductionReferences.
 */
public class SortVariable {
  public SortVariable() {}
}
