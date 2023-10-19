// Copyright (c) K Team. All Rights Reserved.
package org.kframework

import org.kframework.utils.errorsystem.KEMException

import java.util
import collection._
import scala.annotation.tailrec

/**
 * A partially ordered set based on an initial set of direct relations.
 */
class POSet[T](val directRelations: Set[(T, T)]) extends Serializable {
  // convert the input set of relations to Map form for performance
  private val directRelationsMap: Map[T, Set[T]] = directRelations groupBy { _._1 } mapValues { _ map { _._2 } toSet } map identity

  lazy val elements: Set[T] = directRelations.flatMap(a => Set(a._1, a._2))

  lazy val sortedElements: scala.collection.immutable.List[T] = TopologicalSort.tsort(directRelations).toList

  /**
   * Internal private method. Computes the transitive closer of the initial relations.
   * It also checks for cycles during construction and throws an exception if it finds any.
   *
   * The implementation is simple. It links each element to the successors of its successors.
   * TODO: there may be a more efficient algorithm (low priority)
   */
  @tailrec
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
  private def constructAndThrowCycleException(start: T, current: T, path: Seq[T]): Unit = {
    val currentPath = path :+ current
    val succs = directRelationsMap.getOrElse(current, Set())
    if (succs.contains(start)) {
      throw KEMException.compilerError("Illegal circular relation: " + (currentPath :+ start).mkString(" < "))
    }
    succs foreach { constructAndThrowCycleException(start, _, currentPath) }
  }

  /**
   * All the relations of the POSet, including the transitive ones.
   *
   * Concretely, a map from each element of the poset to the set of elements greater than it.
   */
  val relations: Map[T, Set[T]] = transitiveClosure(directRelationsMap)

  /**
   * A map from each element of the poset to the set of elements less than it.
   */
  lazy val relationsOp: Map[T, Set[T]] =
    relations.toSet[(T, Set[T])].flatMap { case (x, ys) => ys.map(_ -> x) }.groupBy(_._1).mapValues(_.map(_._2))

  def <(x: T, y: T): Boolean = relations.get(x).exists(_.contains(y))
  def >(x: T, y: T): Boolean = relations.get(y).exists(_.contains(x))
  def ~(x: T, y: T): Boolean = <(x, y) || <(y, x)

  /**
   * Returns true if x < y
   */
  def lessThan(x: T, y: T): Boolean = <(x, y)
  def lessThanEq(x: T, y: T): Boolean = x == y || <(x, y)
  def directlyLessThan(x: T, y: T): Boolean = directRelationsMap.get(x).exists(_.contains(y))
  /**
   * Returns true if y < x
   */
  def greaterThan(x: T, y: T): Boolean = >(x, y)
  def greaterThanEq(x: T, y: T): Boolean = x == y || >(x, y)
  def directlyGreaterThan(x: T, y: T): Boolean = directRelationsMap.get(y).exists(_.contains(x))
  /**
   * Returns true if y < x or y < x
   */
  def inSomeRelation(x: T, y: T): Boolean = this.~(x, y)
  def inSomeRelationEq(x: T, y: T): Boolean = x == y || this.~(x, y)

  /**
   * Return the set of all upper bounds of the input.
   */
  def upperBounds(sorts: Iterable[T]): Set[T] =
    if (sorts.isEmpty) elements else POSet.upperBounds(sorts, relations)

  /**
   * Return the set of all lower bounds of the input.
   */
  def lowerBounds(sorts: Iterable[T]): Set[T] =
    if (sorts.isEmpty) elements else POSet.upperBounds(sorts, relationsOp)

  lazy val lub: Option[T] = {
    val mins = minimal(upperBounds(elements))
    if (mins.size == 1) Some(mins.head) else None
  }

  lazy val glb: Option[T] = {
    val maxs = maximal(lowerBounds(elements))
    if (maxs.size == 1) Some(maxs.head) else None
  }

  lazy val asOrdering: Ordering[T] = (x: T, y: T) => if (lessThanEq(x, y)) -1 else if (lessThanEq(y, x)) 1 else 0

  /**
    * Return the subset of items from the argument which are not
    * less than any other item.
    */
  def maximal(sorts: Iterable[T]): Set[T] =
    sorts.filter(s1 => !sorts.exists(s2 => lessThan(s1,s2))).toSet

  def maximal(sorts: util.Collection[T]): util.Set[T] = {
    import scala.collection.JavaConverters._
    maximal(sorts.asScala).asJava
  }

  /**
    * Return the subset of items from the argument which are not
    * greater than any other item.
    */
  def minimal(sorts: Iterable[T]): Set[T] =
    sorts.filter(s1 => !sorts.exists(s2 => >(s1,s2))).toSet

  def minimal(sorts: util.Collection[T]): util.Set[T] = {
    import scala.collection.JavaConverters._
    minimal(sorts.asScala).asJava
  }

  override def toString: String = {
    "POSet(" + (relations flatMap { case (from, tos) => tos map { to => from + "<" + to } }).mkString(",") + ")"
  }

  override def hashCode: Int = relations.hashCode()

  override def equals(that: Any): Boolean = that match {
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
    def <(y: T): Boolean = po.<(x, y)
    def >(y: T): Boolean = po.>(x, y)
  }

  /**
   * Return the set of all elements which are greater than or equal to each element of the input,
   * using the provided relations map. Input must be non-empty.
   */
  private def upperBounds[T](sorts: Iterable[T], relations: Map[T, Set[T]]): Set[T] =
    (((sorts filterNot relations.keys.toSet[T]) map {Set.empty + _}) ++
      ((relations filterKeys sorts.toSet) map { case (k, v) => v + k })) reduce { (a, b) => a & b }
}
