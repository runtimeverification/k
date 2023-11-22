package org.kframework.parser

import org.kframework.attributes.Location
import org.kframework.kore.Sort
import org.kframework.kore.SortHead

sealed abstract class BoundedSort

object BoundedSort {
  final case class Constructor(head: SortHead) extends BoundedSort

  final class Variable(val lowerBounds: java.util.List[BoundedSort],
                       val upperBounds: java.util.List[BoundedSort]) extends BoundedSort
}

final case class CompactSort(vars: java.util.Set[BoundedSort.Variable],
                             ctors: java.util.Set[SortHead])

final case class InferenceState(varSorts: java.util.Map[VariableId, BoundedSort],
                                params: java.util.Map[(ProductionReference, Sort), BoundedSort.Variable],
                                constraintCache: java.util.Set[(BoundedSort, BoundedSort)])

final case class InferenceResult[T](sort: T,
                                    varSorts: java.util.Map[VariableId, T])


sealed abstract class VariableId
object VariableId {
  final case class Named(name: String) extends VariableId
  final case class Anon(constant: Constant, id: Integer) extends VariableId
}
