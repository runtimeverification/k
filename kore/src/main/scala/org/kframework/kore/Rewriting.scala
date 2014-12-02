package org.kframework.kore

import KBoolean._

trait Rewriting {
  self: K =>

  import Anywhere._
  /**
   * search using the rewrite rule in K
   */
  def search(rules: Set[KRewrite]): Set[K] = priority(rules) flatMap search

  def priority(rules: Set[KRewrite]): Set[KRewrite] = this match {
    case KApply(KLabel(v), _, _) => rules collect {
      case r @ KRewrite(KApply(v1, _, _), _, _) if v == v1 => r
    }
    case _ => rules
  }

  /**
   * search using the rewrite rule in K
   */
  def search(rewrite: KRewrite): Set[K] = {
    val solutions = rewrite.left.matchAll(this)
    println(solutions)
    solutions map { substituion => rewrite.right.transform(substituion) }
  }

  def transform(substituion: Map[KVariable, K]): K = this match {
    case Anywhere(p) => substituion(TOP).transform(substituion + (HOLE -> p))
    case v: KVariable => substituion(v).transform(substituion)
    case kapp @ KApply(v: KVariable, klist, _) if substituion.contains(v) =>
      val newChildren = klist map { x: K => x.transform(substituion) }
      KApply(substituion(v).asInstanceOf[MetaKLabel].klabel, newChildren)
    case c: KCollection =>
      c map { x: K => x.transform(substituion) }
    case e => e
  }

  def search(rewrite: K): Set[K] = {
    search(KRewrite(toLeft(rewrite), toRight(rewrite)))
  }

  def toLeft(rewrite: K): K = rewrite match {
    case KRewrite(left, right, _) => left
    case c: KCollection => c map toLeft
    case other => other
  }

  def toRight(rewrite: K): K = rewrite match {
    case KRewrite(left, right, _) => right
    case Anywhere(p) => Anywhere(toRight(p))
    case c: KCollection => c map toRight
    case other => other
  }
}
