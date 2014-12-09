package org.kframework.tiny

import org.kframework.kore._
import builtin.KBoolean._
import org.kframework.Term
import org.kframework.Collection
import org.kframework.tiny.Strategy.Rule

object Substitution {
  implicit def apply(self: Term): Substitution = new Substitution(self)
}

class Substitution(self: Term) {
  import Substitution._

  def transform(substituion: Solution): Term = self match {
    case a @ Anywhere(p, _) => substituion(a.TOPVariable).transform(substituion + (a.HOLEVariable -> p))
    case v: KVariable => substituion(v).transform(substituion)
    case kapp @ KApply(v: KVariable, klist, _) if substituion.contains(v) =>
      val newChildren = klist map { x: Term => x.transform(substituion).asInstanceOf[K] }
      KApply(substituion(v).asInstanceOf[MetaKLabel].klabel, newChildren)
    case c: Collection[_] =>
      c.asInstanceOf[Collection[Term]] map { x: Term => x.transform(substituion) }
    case e => e
  }
}

object RewriteToTop {
  def toLeft(rewrite: Term): Term = rewrite match {
    case KRewrite(left, right, _) => left
    case c: Collection[_] => c.asInstanceOf[Collection[Term]] map toLeft
    case other => other
  }

  def toRight(rewrite: Term): Term = rewrite match {
    case KRewrite(left, right, _) => right
    case Anywhere(p, _) => Anywhere(toRight(p))
    case c: Collection[_] => c.asInstanceOf[Collection[Term]] map toRight
    case other => other
  }
}

object Rule {
  import RewriteToTop._

  def apply(termWithRewrite: Term): Rule = {
    val left = toLeft(termWithRewrite)
    val right = toRight(termWithRewrite)

    (t: Term) => {
      val pmSolutions = left.matchAll(t)
      pmSolutions map { substituion => Substitution(right).transform(substituion) }
    }
  }
}

case class Rewritable(self: Term) {
  import RewriteToTop._
  import Anywhere._
  import Substitution._
  /**
   * search using the rewrite rule in Term
   */
  private def search(rules: Set[KRewrite]): Set[Term] = priority(rules) flatMap searchFor

  private def priority(rules: Set[KRewrite]): Set[KRewrite] = self match {
    case KApply(KLabel(v), _, _) => rules collect {
      case r @ KRewrite(KApply(v1, _, _), _, _) if v == v1 => r
    }
    case _ => rules
  }

  def searchFor(rewrite: Term): Set[Term] = {
    Rule(rewrite)(self)
  }
}

object Rewritable {
  implicit def TermToRewriting(self: Term) = Rewritable(self)
}
