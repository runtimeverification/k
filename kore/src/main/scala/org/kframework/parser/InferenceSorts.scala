package org.kframework.parser

import org.kframework.kore.Sort
import org.kframework.kore.SortHead

sealed abstract class BoundedSort

object BoundedSort {
  final case class Constructor(head: SortHead, params: java.util.List[BoundedSort]) extends BoundedSort

  final class Variable(val lowerBounds: java.util.List[BoundedSort],
                       val upperBounds: java.util.List[BoundedSort],
                       val name: java.util.Optional[String]) extends BoundedSort
}

final case class CompactSort(vars: java.util.Set[BoundedSort.Variable],
                             ctors: java.util.Set[(SortHead, java.util.List[CompactSort])])

final case class InferenceState(varSorts: java.util.Map[String, BoundedSort],
                                ambSorts: java.util.Map[Ambiguity, BoundedSort],
                                params: java.util.Map[(ProductionReference, Sort), BoundedSort.Variable],
                                constraintCache: java.util.Set[(BoundedSort, BoundedSort)])

final case class InferenceResult[T](sort: T,
                                    varSorts: java.util.Map[String, T],
                                    ambSorts: java.util.Map[Ambiguity, T])

