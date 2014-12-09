package org.kframework.tiny

import org.kframework._
import org.kframework.kore.KVariable

trait Proposition

trait Equation {
  def left: Term
  def right: Term
}

trait Equivalence {
  def apply(a: Term, b: Term): Boolean
}

object Conjunction {
  def apply(pairs: (KVariable, Term)*): Conjunction = Conjunction(pairs.toMap)
}

case class Conjunction private (bindings: Map[KVariable, Term], other: Set[Equation] = Set()) extends Proposition {
  def ++(other: Conjunction) = Conjunction(bindings ++ other.bindings)
  def +(other: (KVariable, Term)) = Conjunction(bindings + other)

  def and(that: Conjunction): Option[Conjunction] = {
    //  if variables are bound to distinct terms, m1 and m2 is false (none)
    if ((bindings.keys.toSet & that.bindings.keys.toSet).exists(v => bindings(v) != that.bindings(v))) {
      None
    } else
      Some(this ++ that)
  }

  def apply(v: KVariable) = bindings(v)

  def mapValues(f: Term => Term) = Conjunction(bindings mapValues f)

  def contains(v: KVariable) = bindings contains v
}

case class Disjunction(conjunctions: Set[Conjunction]) {
  def or(other: Disjunction): Disjunction =
    Disjunction(conjunctions | other.conjunctions)

  def and(other: Disjunction): Disjunction = {
    Disjunction((for (m1 <- conjunctions; m2 <- other.conjunctions) yield {
      m1 and m2
    }).flatten)
  }

  def headOption = conjunctions.headOption

  def endomap(f: Conjunction => Conjunction) = Disjunction(conjunctions map f)

  def map[T](f: Conjunction => T) = conjunctions map f
}

object Disjunction {
  def apply(conjunctions: Conjunction*): Disjunction = Disjunction(conjunctions.toSet)
}

object EqualsEquivalence extends Equivalence {
  def apply(a: Term, b: Term): Boolean = a == b
}
