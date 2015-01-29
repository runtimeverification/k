package org.kframework.tiny

import org.kframework.koreimplementation.K

object Strategy {
  import Rewritable._
  import Strategy._

  type Rule = K => Set[K]

  case class |(left: Rule, right: Rule) extends Rule {
    def apply(t: K) = { left(t) | right(t) }
  }

  case class &(left: Rule, right: Rule) extends Rule {
    def apply(t: K) = { left(t) & right(t) }
  }

  case class ifthenelse(theIf: Rule, theThen: Rule, theElse: Rule) {
    def apply(t: K) = {
      val appliedIf = theIf(t)
      if (!appliedIf.isEmpty)
        appliedIf flatMap theThen
      else
        theElse(t)
    }
  }

  object id extends Rule { def apply(t: K) = Set(t) }
  object empty extends Rule { def apply(t: K) = Set() }

  def then(left: Rule, right: Rule) = ifthenelse(left, right, id)
  def next(left: Rule, right: Rule) = ifthenelse(left, right, empty)

  case class repeat(r: Rule) extends Rule {
    def apply(t: K) = {
      var res: Set[K] = Set(t); var prevRes: Set[K] = Set()
      do { prevRes = res; res = res flatMap r } while (!res.isEmpty)
      prevRes
    }
  }
}
