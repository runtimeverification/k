package org.kframework.tiny

import org.kframework._
import org.kframework.kore._

import scala.collection.mutable

trait Proposition extends K {
//  def and(p: Proposition): Proposition = Conjunction(this, p)
//  def or(p: Proposition): Proposition = Disjunction(this, p)
}

trait Predicate extends K

trait Equation extends Proposition with Predicate {
  def left: K
  def right: K
}

case class Equals(left: K, right: K, att: Attributes = Attributes()) extends SimpleCaseClass with Equation {
  def matchAll(k: K)(implicit rest: Theory): Disjunction = ???

  override type This = Equals

  override def copy(att: Attributes): This = Equals(left, right, att)
}

case class Binding(variable: KVariable, value: K, att: Attributes = Attributes()) extends SimpleCaseClass with Equation {
  val left = variable
  val right = value
  override type This = Binding

  override def matchAll(k: K)(implicit rest: Theory): Disjunction = ???

  override def copy(att: Attributes): This = Binding(variable, value, att)
}

trait TruthValue

object True extends Conjunction(Set(), Map()) with TruthValue {
  override def toString = "True"
}

object False extends Disjunction(Set()) with TruthValue {
  override def toString = "False"
}

trait Theory {
  /**
   * Tells whether the proposition is valid in this theory.
   * If we cannot find an answer (e.g., we have symbolic values), return None
   */
  def apply(proposition: Proposition): Option[TruthValue]

  /**
   * Helper method
   */
  def apply(left: K, right: K): Boolean = apply(Equals(left, right)) == Some(True)
}

case class ExtendedTheory(base: Theory, extra: Proposition) {
  def apply(proposition: Proposition): Option[TruthValue] = {
//    base.apply(Conjunction(proposition, extra))
    ???
  }
}

object Conjunction {
  def apply(pairs: (KVariable, K)*): Conjunction = Conjunction(Set[Proposition](), pairs.toMap)
}

case class Conjunction(propositions: Set[Proposition], bindings: Map[KVariable, K]) extends Proposition {
  def and(that: Conjunction): Option[Conjunction] = {
    //  if variables are bound to distinct terms, m1 and m2 is false (none)
    if ((bindings.keys.toSet & that.bindings.keys.toSet).exists(v => bindings(v) != that.bindings(v))) {
      None
    } else
      Some(Conjunction(propositions ++ that.propositions, bindings ++ that.bindings))
  }

  def apply(v: KVariable) = bindings(v)

  def mapValues(f: K => K) = Conjunction(propositions, bindings mapValues f)

  def contains(v: KVariable) = bindings contains v

  override def toString =
    if (bindings.size == 0 && propositions.size == 0)
      "True"
    else {
      val bindingsString = bindings map { case (k, v) => k + "=" + v } mkString "  /\\  "
      val otherString = propositions mkString "  /\\  "
      if (bindingsString != "" && otherString != "")
        bindingsString + "  /\\  " + otherString
      else
        bindingsString + otherString
    }

  override protected type This = this.type

  override def transform(t: PartialFunction[K, K]): K = ???

  override def copy(att: Attributes): This = ???

  override def matchAll(k: K)(implicit rest: Theory): Disjunction = ???

  override def att: Attributes = ???
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

  override def toString =
    if (conjunctions.size == 0)
      "False"
    else
      conjunctions mkString "  \\/  "
}

object Disjunction {
  def apply(conjunctions: Conjunction*): Disjunction = Disjunction(conjunctions.toSet)
}

object FreeTheory extends Theory {
  /**
   * Tells whether the proposition is valid in this theory.
   * If we cannot find an answer (e.g., we have symbolic values), return None
   */
  override def apply(proposition: Proposition): Option[TruthValue] = proposition match {
    case Equals(left, right, _) => Some(if (left == right) True else False)
    case _ => Some(False)
  }
}


