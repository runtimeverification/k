package org.kframework.tiny

import org.kframework._
import org.kframework.kore.KVariable

trait Proposition

trait Equation {
  def left: Term
  def right: Term
}

case class Problem(equations: Set[Equation])

object Solution {
  def apply(pairs: (KVariable, Term)*): Solution = Solution(pairs.toMap)
}

case class Solution private (m: Map[KVariable, Term]) extends Proposition {
  def ++(other: Solution) = Solution(m ++ other.m)
  def +(other: (KVariable, Term)) = Solution(m + other)

  def and(that: Solution): Option[Solution] = {
    //  if variables are bound to distinct terms, m1 and m2 is false (none)
    if ((m.keys.toSet & that.m.keys.toSet).exists(v => m(v) != that.m(v))) {
      None
    } else
      Some(this ++ that)
  }

  def apply(v: KVariable) = m(v)

  def mapValues(f: Term => Term) = Solution(m mapValues f)

  def contains(v: KVariable) = m contains v
}

trait BindingOps {
  def or(s1: Set[Solution], s2: Set[Solution]): Set[Solution] =
    s1 | s2

  def and(s1: Set[Solution], s2: Set[Solution]): Set[Solution] = {
    (for (m1 <- s1; m2 <- s2) yield {
      m1 and m2
    }).flatten
  }
}

trait Equivalence {
  def apply(a: Term, b: Term): Boolean
}

object EqualsEquivalence extends Equivalence {
  def apply(a: Term, b: Term): Boolean = a == b
}
