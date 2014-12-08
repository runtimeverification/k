package org.kframework.tiny

import org.kframework.kore._
import builtin.KBoolean._
import org.kframework.Term
import org.kframework.Collection

trait Rewriting {
  self: Term =>

  import Anywhere._
  /**
   * search using the rewrite rule in Term
   */
  def search(rules: Set[KRewrite]): Set[Term] = priority(rules) flatMap search

  def priority(rules: Set[KRewrite]): Set[KRewrite] = this match {
    case KApply(KLabel(v), _, _) => rules collect {
      case r @ KRewrite(KApply(v1, _, _), _, _) if v == v1 => r
    }
    case _ => rules
  }

  /**
   * search using the rewrite rule in Term
   */
  def search(left: Term, right: Term): Set[Term] = {
    val solutions = left.matchAll(this)
    solutions map { substituion => right.transform(substituion) }
  }

  def transform(substituion: Map[KVariable, Term]): Term = this match {
    case Anywhere(p) => substituion(TOP).transform(substituion + (HOLE -> p))
    case v: KVariable => substituion(v).transform(substituion)
    case kapp @ KApply(v: KVariable, klist, _) if substituion.contains(v) =>
      val newChildren = klist map { x: Term => x.transform(substituion).asInstanceOf[K] }
      KApply(substituion(v).asInstanceOf[MetaKLabel].klabel, newChildren)
    case c: Collection[_] =>
      c.asInstanceOf[Collection[Term]] map { x: Term => x.transform(substituion) }
    case e => e
  }

  def search(rewrite: Term): Set[Term] = {
    search(toLeft(rewrite), toRight(rewrite))
  }

  def toLeft(rewrite: Term): Term = rewrite match {
    case KRewrite(left, right, _) => left
    case c: Collection[_] => c.asInstanceOf[Collection[Term]] map toLeft
    case other => other
  }

  def toRight(rewrite: Term): Term = rewrite match {
    case KRewrite(left, right, _) => right
    case Anywhere(p) => Anywhere(toRight(p))
    case c: Collection[_] => c.asInstanceOf[Collection[Term]] map toRight
    case other => other
  }
}
