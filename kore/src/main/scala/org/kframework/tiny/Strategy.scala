package org.kframework.tiny

import org.kframework.Term

object Strategy {
  import Rewritable._
  import Strategy._

  type Rule = Term => Set[Term]

  case class |(left: Rule, right: Rule) extends Rule {
    def apply(t: Term) = { left(t) | right(t) }
  }

  case class &(left: Rule, right: Rule) extends Rule {
    def apply(t: Term) = { left(t) & right(t) }
  }

  case class ifthenelse(theIf: Rule, theThen: Rule, theElse: Rule) {
    def apply(t: Term) = {
      val appliedIf = theIf(t)
      if (!appliedIf.isEmpty)
        appliedIf flatMap theThen
      else
        theElse(t)
    }
  }

  object id extends Rule { def apply(t: Term) = Set(t) }
  object empty extends Rule { def apply(t: Term) = Set() }

  def then(left: Rule, right: Rule) = ifthenelse(left, right, id)
  def next(left: Rule, right: Rule) = ifthenelse(left, right, empty)

  case class repeat(r: Rule) extends Rule {
    def apply(t: Term) = {
      var res: Set[Term] = Set(t); var prevRes: Set[Term] = Set()
      do { prevRes = res; res = res flatMap r } while (!res.isEmpty)
      prevRes
    }
  }
}
