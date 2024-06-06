// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner.disambiguation.inference;

import static org.kframework.Collections.*;

import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.kframework.POSet;
import org.kframework.builtin.Sorts;
import org.kframework.kore.Sort;
import org.kframework.kore.SortHead;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

/**
 * A sort which, depending on the polarity where it occurs, represents either an intersection or a
 * union of component sorts (variables and constructors). Analogous to CompactType from SimpleSub.
 */
public record CompactSort(Set<SortVariable> vars, Set<SortHead> ctors) {

  public CompactSort(SortVariable var) {
    this(Stream.of(var).collect(Collectors.toCollection(HashSet::new)), new HashSet<>());
  }

  /**
   * Compact a BoundedSort, converting all transitive bounds into a single intersection / union.
   *
   * @param sort - The BoundedSort to make compact
   * @param polarity - The polarity where sort occurs. True for positive, false for negative.
   * @return A CompactSort containing all bounds represented by sort
   */
  public static CompactSort makeCompact(BoundedSort sort, boolean polarity) {
    if (sort instanceof BoundedSort.Constructor ctor) {
      if (ctor.head().params() == 0) {
        Set<SortHead> ctors = new HashSet<>();
        ctors.add(ctor.head());
        return new CompactSort(new HashSet<>(), ctors);
      }
      throw new AssertionError("Parametric sorts are not yet supported!");
    }

    BoundedSort.Variable var = (BoundedSort.Variable) sort;
    Set<BoundedSort> bounds = polarity ? var.lowerBounds() : var.upperBounds();

    Set<SortVariable> vars = new HashSet<>();
    Set<SortHead> ctors = new HashSet<>();
    vars.add(var.sortVar());
    for (BoundedSort bound : bounds) {
      CompactSort compactBound = makeCompact(bound, polarity);
      vars.addAll(compactBound.vars());
      ctors.addAll(compactBound.ctors());
    }
    return new CompactSort(vars, ctors);
  }

  /**
   * Substitute variables for CompactSorts.
   *
   * @param subst - A map where an entry v |-> Optional.of(t) indicates that the variable v should
   *     be replaced by t, and an entry v |-> Optional.empty() indicates that v should be removed
   *     entirely (effectively, replacing it with top or bottom depending on polarity).
   * @return A new CompactSort with the substitution applied
   */
  public CompactSort substitute(Map<SortVariable, Optional<CompactSort>> subst) {
    Set<SortVariable> newVars = new HashSet<>();
    Set<SortHead> newCtors = new HashSet<>(ctors);
    for (SortVariable var : vars) {
      if (!subst.containsKey(var)) {
        newVars.add(var);
        continue;
      }
      if (subst.get(var).isPresent()) {
        CompactSort newSort = subst.get(var).get();
        newVars.addAll(newSort.vars());
        newCtors.addAll(newSort.ctors());
      }
    }
    return new CompactSort(newVars, newCtors);
  }

  /**
   * An error indicating that we could not compute a type meet or join.
   *
   * @param sorts - The set of sorts we are trying to meet/join.
   * @param candidates - The set of minimal upper bounds / maximal lower bounds of sorts.
   * @param polarity - True for positive, false for negative
   */
  public record LatticeOpError(Set<Sort> sorts, Set<Sort> candidates, boolean polarity) {}

  /**
   * Convert to an equivalent Sort, instantiating variables and actually computing the type
   * join/meet on the provided subsort.
   *
   * @param polarity - The polarity where this CompactSort occurs.
   * @param instantiation - A map indicating how variables should be instantiated
   * @param subsorts - The Sort poset
   * @return An equivalent Sort
   */
  public Either<LatticeOpError, Sort> asSort(
      boolean polarity, Map<SortVariable, Sort> instantiation, POSet<Sort> subsorts) {
    Set<Sort> sorts = vars.stream().map(instantiation::get).collect(Collectors.toSet());
    sorts.addAll(
        ctors.stream()
            .map(h -> new org.kframework.kore.ADT.Sort(h.name(), Seq()))
            .collect(Collectors.toSet()));
    // WLOG upper/lower bound of a set is the upper/lower bound of its maximal/minimal elements.
    // This is useful to prune the search space as the POSet operations can be quite expensive
    sorts = polarity ? subsorts.maximal(sorts) : subsorts.minimal(sorts);
    if (sorts.size() == 1) {
      return Right.apply(sorts.iterator().next());
    }
    Set<Sort> bounds = polarity ? subsorts.upperBounds(sorts) : subsorts.lowerBounds(sorts);
    bounds.removeIf(s -> subsorts.lessThanEq(s, Sorts.KBott()));
    Set<Sort> candidates = polarity ? subsorts.minimal(bounds) : subsorts.maximal(bounds);
    if (candidates.size() != 1) {
      return Left.apply(new LatticeOpError(sorts, candidates, polarity));
    }
    return Right.apply(candidates.iterator().next());
  }
}
