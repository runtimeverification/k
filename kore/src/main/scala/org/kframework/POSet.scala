package org.kframework

import org.kframework.kore.Sort

class POSet[T](directRelations: Set[(T, T)]) {

  // TODO: there may be a more efficient algorithm (low priority)
  private def transitiveClosure(relations: Map[T, Set[T]]): Map[T, Set[T]] = {
    val newRelations = relations map {
      case (start, succ) => (start, succ | (succ flatMap { relations.get(_).getOrElse(Set()) }))
    }
    if (relations != newRelations) transitiveClosure(newRelations) else relations
  }

  private val directRelationsMap = directRelations groupBy { _._1 } mapValues { _ map { _._2 } toSet }

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
    "POSet(" + (relations map { case (from, tos) => tos map { case to => from + "<" + to } }).mkString(",") + ")"
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
