// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner.disambiguation.inference;

import static org.kframework.Collections.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.kframework.POSet;
import org.kframework.builtin.Sorts;
import org.kframework.kore.Sort;
import org.kframework.parser.Constant;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.Term;
import scala.Tuple2;

/**
 * A driver which manages all state during the initial phase of SortInferencer where we infer
 * unsimplified BoundedSorts.
 */
public final class InferenceDriver {
  /** The POSet of sorts ordered by the sub-sort relation. */
  private final POSet<Sort> subsorts;

  /** A unique sort variable for every variable that inference encounters. */
  private final Map<VariableId, BoundedSort.Variable> varSorts = new HashMap<>();

  /** A unique sort variable for every parameter that inference encounters. */
  private final Map<ParamId, BoundedSort.Variable> paramSorts = new HashMap<>();

  /**
   * A cache of all subtyping constraints that have already been processed. Pairs (t1, t2) represent
   * a constraint t1 <: t2.
   */
  private final Set<Tuple2<BoundedSort, BoundedSort>> constraintCache = new HashSet<>();

  public InferenceDriver(POSet<Sort> subsorts) {
    this.subsorts = subsorts;
  }

  /**
   * Get the BoundedSort.Variable instance for a variable. Unlike SimpleSub, we don't have explicit
   * binders at the top of the Term introducing every variable, so these BoundedSort.Variable
   * instances must be created on the fly when each variable is first encountered during inference.
   */
  public BoundedSort varSort(Constant var) {
    VariableId varId = VariableId.apply(var);
    if (!varSorts.containsKey(varId)) {
      // Every variable must be assigned a user sort <=K
      BoundedSort.Variable sort = new BoundedSort.Variable();
      sort.upperBounds().add(sortToBoundedSort(Sorts.K(), null));
      varSorts.put(varId, sort);
    }
    return varSorts.get(varId);
  }

  /**
   * Convert a Sort to a BoundedSort, which may be a sort parameter from the provided
   * ProductionReference.
   *
   * @param sort - The Sort to convert
   * @param prOrNull - The ProductionReference where this Sort occurs, or null if sort is guaranteed
   *     not to be a sort parameter.
   * @return A BoundedSort representing sort
   */
  public BoundedSort sortToBoundedSort(Sort sort, ProductionReference prOrNull) {
    if (prOrNull != null && prOrNull.production().params().contains(sort)) {
      ParamId paramId = new ParamId(prOrNull, sort);
      if (!paramSorts.containsKey(paramId)) {
        paramSorts.put(paramId, new BoundedSort.Variable());
      }
      return paramSorts.get(paramId);
    }
    return new BoundedSort.Constructor(sort.head());
  }

  public BoundedSort returnSort(ProductionReference pr) throws ConstraintError {
    BoundedSort resSort = new BoundedSort.Variable();
    constrain(sortToBoundedSort(pr.production().sort(), pr), resSort, pr);
    return resSort;
  }

  /**
   * Update sub-/super-type constraints to record the fact that lhs <: rhs.
   *
   * @param pr - The ProductionReference where this constraint originated. This is only necessary
   *     for error reporting.
   * @throws ConstraintError - An error if lhs <: rhs induces some subsort relation which is invalid
   *     based on the subsort poset.
   */
  public void constrain(BoundedSort lhs, BoundedSort rhs, ProductionReference pr)
      throws ConstraintError {
    // This cache is necessary to prevent exponential blow-up and avoid loops like
    // loops like a <: b <: a <: b ...
    if (lhs.equals(rhs) || constraintCache.contains(Tuple2.apply(lhs, rhs))) {
      return;
    }

    if (lhs instanceof BoundedSort.Variable lhsVar) {
      constraintCache.add(Tuple2.apply(lhs, rhs));
      lhsVar.upperBounds().add(rhs);
      for (BoundedSort lhsLower : lhsVar.lowerBounds()) {
        constrain(lhsLower, rhs, pr);
      }
      return;
    }

    if (rhs instanceof BoundedSort.Variable rhsVar) {
      constraintCache.add(Tuple2.apply(lhs, rhs));
      rhsVar.lowerBounds().add(lhs);
      for (BoundedSort rhsUpper : rhsVar.upperBounds()) {
        constrain(lhs, rhsUpper, pr);
      }
      return;
    }

    // If they are primitive sorts, we can check the sort poset directly
    BoundedSort.Constructor lhsCtor = (BoundedSort.Constructor) lhs;
    BoundedSort.Constructor rhsCtor = (BoundedSort.Constructor) rhs;
    if (lhsCtor.head().params() == 0 && rhsCtor.head().params() == 0) {
      Sort lhsSort = new org.kframework.kore.ADT.Sort(lhsCtor.head().name(), Seq());
      Sort rhsSort = new org.kframework.kore.ADT.Sort(rhsCtor.head().name(), Seq());
      if (subsorts.lessThanEq(lhsSort, rhsSort)) {
        return;
      }
      throw new ConstraintError(lhsSort, rhsSort, pr);
    }

    throw new AssertionError("Parametric sorts are not yet supported!");
  }

  /**
   * After inference is complete, get the final TermSort result recording the sorts of variables.
   *
   * @param term - The term that we ran the driver on.
   * @param sort - The inferred sort of the overall term.
   */
  public TermSort<BoundedSort> getResult(Term term, BoundedSort sort) {
    return new TermSort<>(term, sort, varSorts);
  }
}
