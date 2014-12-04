package org.kframework.kore

import KBoolean._
import org.kframework.Top
import org.kframework.Collection

trait Rewriting {
  self: Top =>

  import Anywhere._
  /**
   * search using the rewrite rule in Top
   */
  def search(rules: Set[KRewrite]): Set[Top] = priority(rules) flatMap search

  def priority(rules: Set[KRewrite]): Set[KRewrite] = this match {
    case KApply(KLabel(v), _, _) => rules collect {
      case r @ KRewrite(KApply(v1, _, _), _, _) if v == v1 => r
    }
    case _ => rules
  }

  /**
   * search using the rewrite rule in Top
   */
  def search(left: Top, right: Top): Set[Top] = {
    val solutions = left.matchAll(this)
    println(solutions)
    solutions map { substituion => right.transform(substituion) }
  }

  def transform(substituion: Map[KVariable, Top]): Top = this match {
    case Anywhere(p) => substituion(TOP).transform(substituion + (HOLE -> p))
    case v: KVariable => substituion(v).transform(substituion)
    case kapp @ KApply(v: KVariable, klist, _) if substituion.contains(v) =>
      val newChildren = klist map { x: Top => x.transform(substituion).asInstanceOf[K] }
      KApply(substituion(v).asInstanceOf[MetaKLabel].klabel, newChildren)
    case c: Collection[Top] =>
      c map { x: Top => x.transform(substituion) }
    case e => e
  }

  def search(rewrite: Top): Set[Top] = {
    search(toLeft(rewrite), toRight(rewrite))
  }

  def toLeft(rewrite: Top): Top = rewrite match {
    case KRewrite(left, right, _) => left
    case c: Collection[Top] => c map toLeft
    case other => other
  }

  def toRight(rewrite: Top): Top = rewrite match {
    case KRewrite(left, right, _) => right
    case Anywhere(p) => Anywhere(toRight(p))
    case c: Collection[Top] => c map toRight
    case other => other
  }
}
