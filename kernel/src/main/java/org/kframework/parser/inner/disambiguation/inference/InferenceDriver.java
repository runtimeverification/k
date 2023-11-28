package org.kframework.parser.inner.disambiguation.inference;

import static org.kframework.Collections.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.kframework.POSet;
import org.kframework.kore.Sort;
import org.kframework.parser.Constant;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.Term;
import scala.Tuple2;

public final class InferenceDriver {
  private final POSet<Sort> subsorts;
  private final Map<VariableId, BoundedSort> varSorts = new HashMap<>();
  private final Map<ParamId, BoundedSort.Variable> paramSorts = new HashMap<>();
  private final Set<Tuple2<BoundedSort, BoundedSort>> constraintCache = new HashSet<>();

  public InferenceDriver(POSet<Sort> subsorts) {
    this.subsorts = subsorts;
  }

  public BoundedSort varSort(Constant var) {
    VariableId varId = VariableId.apply(var);
    if (!varSorts.containsKey(varId)) {
      varSorts.put(varId, new BoundedSort.Variable());
    }
    return varSorts.get(varId);
  }

  /**
   * Convert a Sort to a BoundedSort
   *
   * @param sort - The Sort to convert
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

  public void constrain(BoundedSort lhs, BoundedSort rhs, ProductionReference pr)
      throws ConstraintError {
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

  public TermSort<BoundedSort> getResult(Term term, BoundedSort sort) {
    return new TermSort<>(term, sort, varSorts);
  }
}
