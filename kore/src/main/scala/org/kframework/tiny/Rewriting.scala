package org.kframework.tiny

import org.kframework.kore._
import builtin.KBoolean._
import org.kframework.Collection
import org.kframework.tiny.Strategy.Rule

object Substitution {
  implicit def apply(self: K): Substitution = new Substitution(self)
}

class Substitution(self: K) {
  import Substitution._

  def transform(substituion: Map[KVariable, K]): K = {
    (doSubstitution _).andThen(flattenInjections)(substituion)
  }

  private def flattenInjections(term: K): K = term.transform({
    case KApply(l, kl, att) =>
      KApply(l, InjectedKList.flattenKList(kl) map flattenInjections _, att)
  })

  private def doSubstitution(substituion: Map[KVariable, K]) =
    self match {
      case a @ Anywhere(p, _) => substituion(a.TOPVariable).transform(substituion + (a.HOLEVariable -> p))
      case v: KVariable => substituion(v).transform(substituion)
      case kapp @ KApply(v: KVariable, klist, _) if substituion.contains(v) =>
        val newChildren = klist map { x: K => x.transform(substituion).asInstanceOf[K] }
        KApply(substituion(v).asInstanceOf[MetaKLabel].klabel, newChildren)
      case c: Collection[_] =>
        c.asInstanceOf[KCollection] map { x: K => x.transform(substituion) }
      case e => e
    }
}

object RewriteToTop {
  def toLeft(rewrite: K): K = rewrite match {
    case KRewrite(left, right, _) => left
    case c: KCollection => c map toLeft
    case other => other
  }

  def toRight(rewrite: K): K = rewrite match {
    case KRewrite(left, right, _) => right
    case Anywhere(p, _) => Anywhere(toRight(p))
    case c: KCollection => c map toRight
    case other => other
  }
}

object Rule {
  import RewriteToTop._

  def apply(termWithRewrite: K)(implicit theory: Theory = FreeTheory): Rule = {
    val left = toLeft(termWithRewrite)
    val right = toRight(termWithRewrite)

    (t: K) => {
      val pmSolutions = left.matchAll(t)
      pmSolutions map { substituion => Substitution(right).transform(substituion.bindings) }
    }
  }
}

case class Rewritable(self: K) {
  import RewriteToTop._
  import Anywhere._
  import Substitution._
  /**
   * search using the rewrite rule in K
   */
  private def search(rules: Set[KRewrite])(implicit theory: Theory): Set[K] = priority(rules) flatMap searchFor

  private def priority(rules: Set[KRewrite]): Set[KRewrite] = self match {
    case KApply(KLabel(v), _, _) => rules collect {
      case r @ KRewrite(KApply(v1, _, _), _, _) if v == v1 => r
    }
    case _ => rules
  }

  def searchFor(rewrite: K)(implicit theory: Theory): Set[K] = {
    Rule(rewrite)(theory)(self)
  }
}

object Rewritable {
  implicit def KToRewriting(self: K) = Rewritable(self)
}
