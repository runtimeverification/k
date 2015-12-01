// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework

import java.util
import java.util.Optional
import collection._

case class CircularityException[T](cycle: Seq[T]) extends Exception(cycle.mkString(" < "))

/**
 * A partially ordered set based on an initial set of direct relations.
 */
class POSet[T](directRelations: Set[(T, T)]) extends Serializable {

  // convert the input set of relations to Map form for performance
  private val directRelationsMap: Map[T, Set[T]] = directRelations groupBy { _._1 } mapValues { _ map { _._2 } toSet } map identity

  /**
   * Internal private method. Computes the transitive closer of the initial relations.
   * It also checks for cycles during construction and throws an exception if it finds any.
   *
   * The implementation is simple. It links each element to the successors of its successors.
   * TODO: there may be a more efficient algorithm (low priority)
   */
  private def transitiveClosure(relations: Map[T, Set[T]]): Map[T, Set[T]] = {
    val newRelations = relations map {
      case (start, succ) =>
        val newSucc = succ flatMap { relations.getOrElse(_, Set()) }
        if (newSucc.contains(start))
          constructAndThrowCycleException(start, start, Seq())
        (start, succ | newSucc)
    }
    if (relations != newRelations) transitiveClosure(newRelations) else relations
  }

  /**
   * Recursive method constructing and throwing and the cycle exception.
   *
   * @param start (or tail) element to look for when constructing the cycle
   * @param current element
   * @param path so far
   */
  private def constructAndThrowCycleException(start: T, current: T, path: Seq[T]) {
    val currentPath = path :+ current
    val succs = directRelationsMap.getOrElse(current, Set())
    if (succs.contains(start))
      throw new CircularityException(currentPath :+ start)

    succs foreach { constructAndThrowCycleException(start, _, currentPath) }
  }

  /**
   * All the relations of the POSet, including the transitive ones.
   */
  val relations = transitiveClosure(directRelationsMap)

  def <(x: T, y: T): Boolean = relations.get(x).exists(_.contains(y))
  def >(x: T, y: T): Boolean = relations.get(y).exists(_.contains(x))
  def ~(x: T, y: T) = <(x, y) || <(y, x)

  /**
   * Returns true if x < y
   */
  def lessThan(x: T, y: T): Boolean = <(x, y)
  def lessThanEq(x: T, y: T): Boolean = <(x, y) | x == y
  def directlyLessThan(x: T, y: T): Boolean = directRelationsMap.get(x).exists(_.contains(y))
  /**
   * Returns true if y < x
   */
  def greaterThan(x: T, y: T): Boolean = >(x, y)
  def greaterThanEq(x: T, y: T): Boolean = >(x, y) | x == y
  def directlyGreaterThan(x: T, y: T): Boolean = directRelationsMap.get(y).exists(_.contains(x))
  /**
   * Returns true if y < x or y < x
   */
  def inSomeRelation(x: T, y: T) = this.~(x, y)
  def inSomeRelationEq(x: T, y: T) = this.~(x, y) | x == y

  /**
   * Returns an Optional of the least upper bound if it exists, or an empty Optional otherwise.
   */
  lazy val leastUpperBound: Optional[T] = lub match {
    case Some(x) => Optional.of(x)
    case None => Optional.empty()
  }

  lazy val lub: Option[T] = {
    val candidates = relations.values reduce { (a, b) => a & b }

    if (candidates.size == 0)
      None
    else if (candidates.size == 1)
      Some(candidates.head)
    else {
      val allPairs = for (a <- candidates; b <- candidates) yield { (a, b) }
      if (allPairs exists { case (a, b) => ! ~(a, b) })
        None
      else
        Some(
          candidates.min(new Ordering[T]() {
            def compare(x: T, y: T) = if (x < y) -1 else if (x > y) 1 else 0
          }))
    }
  }

  /** Return the subset of items from the argument which are not
    * less then any other item.
    */
  def maximal(sorts : Iterable[T]) : Set[T] =
    sorts.filter(s1 => !sorts.exists(s2 => lessThan(s1,s2))).toSet

  def maximal(sorts : util.Collection[T]) : util.Set[T] = {
    import scala.collection.JavaConversions._
    maximal(sorts : Iterable[T])
  }

  override def toString() = {
    "POSet(" + (relations flatMap { case (from, tos) => tos map { case to => from + "<" + to } }).mkString(",") + ")"
  }

  override def hashCode = relations.hashCode()

  override def equals(that: Any) = that match {
    case that: POSet[_] => relations == that.relations
    case _ => false
  }
}

object POSet {
  def apply[T](relations: (T, T)*) = new POSet(relations.toSet)
  def apply[T](s: Set[(T, T)]) = new POSet(s)

  /**
   * Import this for Scala syntactic sugar.
   */
  implicit class PO[T](x: T)(implicit val po: POSet[T]) {
    def <(y: T) = po.<(x, y)
    def >(y: T) = po.>(x, y)
  }
}
