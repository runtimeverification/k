package org.kframework

import org.kframework.kore.Sort

case class CircularityException[T](cycle: Seq[T]) extends Exception(cycle.mkString(" < "))

class POSet[T](directRelations: Set[(T, T)]) {

  private val directRelationsMap = directRelations groupBy { _._1 } mapValues { _ map { _._2 } toSet }
  // TODO: there may be a more efficient algorithm (low priority)
  private def transitiveClosure(relations: Map[T, Set[T]]): Map[T, Set[T]] = {
    val newRelations = relations map {
      case (start, succ) =>
        val newSucc = (succ flatMap { relations.get(_).getOrElse(Set()) })
        if (newSucc.contains(start))
          detectCycle(start, start, Seq())
        (start, succ | newSucc)
    }
    if (relations != newRelations) transitiveClosure(newRelations) else relations
  }

  private def detectCycle(start: T, current: T, path: Seq[T]) {
    val currentPath = path :+ current
    val succs = directRelationsMap(current)
    if (succs.contains(start))
      throw new CircularityException(currentPath :+ start)

    succs foreach { detectCycle(start, _, currentPath) }
  }

  val relations = transitiveClosure(directRelationsMap)

  def <(x: T, y: T): Boolean = relations.get(x) map { _.contains(y) } getOrElse (false)
  def >(x: T, y: T): Boolean = relations.get(y) map { _.contains(x) } getOrElse (false)
  def ~(x: T, y: T) = <(x, y) || <(y, x)

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

  implicit class PO[T](x: T)(implicit val po: POSet[T]) {
    def <(y: T) = po.<(x, y)
    def >(y: T) = po.>(x, y)
  }
}
