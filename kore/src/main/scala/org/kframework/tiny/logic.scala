package org.kframework.tiny

import org.kframework._
import org.kframework.kore.KVariable
import org.kframework.kore.K

trait Proposition

trait Equation {
  def left: K
  def right: K
}

trait Equivalence {
  def apply(a: K, b: K): Boolean
}

object Conjunction {
  def apply(pairs: (KVariable, K)*): Conjunction = Conjunction(pairs.toMap)
}

case class Conjunction private (bindings: Map[KVariable, K], other: Set[Equation] = Set()) extends Proposition {
  def ++(other: Conjunction) = Conjunction(bindings ++ other.bindings)
  def +(other: (KVariable, K)) = Conjunction(bindings + other)

  def and(that: Conjunction): Option[Conjunction] = {
    //  if variables are bound to distinct terms, m1 and m2 is false (none)
    if ((bindings.keys.toSet & that.bindings.keys.toSet).exists(v => bindings(v) != that.bindings(v))) {
      None
    } else
      Some(this ++ that)
  }

  def apply(v: KVariable) = bindings(v)

  def mapValues(f: K => K) = Conjunction(bindings mapValues f)

  def contains(v: KVariable) = bindings contains v

  override def toString =
    if (bindings.size == 0 && other.size == 0)
      "True"
    else {
      val bindingsString = bindings map { case (k, v) => k + "=" + v } mkString "  /\\  "
      val otherString = other mkString "  /\\  "
      if (bindingsString != "" && otherString != "")
        bindingsString + "  /\\  " + otherString
      else
        bindingsString + otherString
    }
}

case class Disjunction(conjunctions: Set[Conjunction])(implicit equivalence: Equivalence) {
  def or(other: Disjunction): Disjunction =
    Disjunction(conjunctions | other.conjunctions)

  def and(other: Disjunction): Disjunction = {
    Disjunction((for (m1 <- conjunctions; m2 <- other.conjunctions) yield {
      m1 and m2
    }).flatten)
  }

  val equiv = equivalence

  def headOption = conjunctions.headOption

  def endomap(f: Conjunction => Conjunction) = Disjunction(conjunctions map f)

  def map[T](f: Conjunction => T) = conjunctions map f

  override def toString =
    if (conjunctions.size == 0)
      "False"
    else
      conjunctions mkString "  \\/  "
}

object Disjunction {
  def apply(conjunctions: Conjunction*)(implicit inScope: Disjunction): Disjunction = Disjunction(conjunctions.toSet)(inScope.equiv)
}

object EqualsEquivalence extends Equivalence {
  def apply(a: K, b: K): Boolean = a == b
}

object Logic {
  def True(implicit disjunction: Disjunction) = Disjunction(Conjunction())(disjunction)
  def False(implicit disjunction: Disjunction) = Disjunction()(disjunction)
}
