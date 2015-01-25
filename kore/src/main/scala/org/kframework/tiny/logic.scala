package org.kframework.tiny

import org.kframework._
import org.kframework.kore._

import scala.collection.mutable

trait Proposition extends K {
  //  def and(p: Proposition): Proposition = Conjunction(this, p)
  //  def or(p: Proposition): Proposition = Disjunction(this, p)
}

trait Predicate extends Proposition

trait Equation extends Proposition with Predicate {
  def left: K

  def right: K
}

case class Equals(left: K, right: K, att: Attributes = Attributes()) extends SimpleCaseClass with Equation {
  def matchAll(k: K)(implicit rest: Theory): Or = ???

  override type This = Equals

  override def copy(att: Attributes): This = Equals(left, right, att)
}

case class Binding(variable: KVariable, value: K, att: Attributes = Attributes()) extends SimpleCaseClass with Equation {
  val left = variable
  val right = value
  override type This = Binding

  override def matchAll(k: K)(implicit rest: Theory): Or = ???

  override def copy(att: Attributes): This = Binding(variable, value, att)
}

trait TruthValue

object True extends And(Set(), Map()) with TruthValue {
  override def toString = "True"
}

object False extends Or(Set()) with TruthValue {
  override def toString = "False"
}

trait Theory {
  /**
   * Tells whether the proposition is valid in this theory.
   * If we cannot find an answer (e.g., we have symbolic values), return None
   * So None means the Proposition is satisfiable.
   */
  def apply(proposition: Proposition): Option[TruthValue]

  /**
   * Helper method
   */
  def apply(left: K, right: K): Boolean = apply(Equals(left, right)) == Some(True)
}

case class PropositionTheory(p: Proposition) extends Theory {
  def apply(proposition: Proposition): Option[TruthValue] =
    FreeTheory.apply(proposition) orElse FreeTheory(???)
}

object And {
  def apply(pairs: (KVariable, K)*): And = And(Set[Predicate](), pairs.toMap)
}

case class And(predicates: Set[Predicate], bindings: Map[KVariable, K]) extends Proposition {
  def and(that: And): Option[And] = {
    //  if variables are bound to distinct terms, m1 and m2 is false (none)
    if ((bindings.keys.toSet & that.bindings.keys.toSet).exists(v => bindings(v) != that.bindings(v))) {
      None
    } else
      Some(And(predicates ++ that.predicates, bindings ++ that.bindings))
  }

  def apply(v: KVariable) = bindings(v)

  def mapValues(f: K => K) = And(predicates, bindings mapValues f)

  def contains(v: KVariable) = bindings contains v

  override def toString =
    if (bindings.size == 0 && predicates.size == 0)
      "True"
    else {
      val bindingsString = bindings map { case (k, v) => k + "=" + v } mkString "  /\\  "
      val otherString = predicates mkString "  /\\  "
      if (bindingsString != "" && otherString != "")
        bindingsString + "  /\\  " + otherString
      else
        bindingsString + otherString
    }

  override protected type This = this.type

  override def transform(t: PartialFunction[K, K]): K = ???

  override def copy(att: Attributes): This = ???

  override def matchAll(k: K)(implicit rest: Theory): Or = ???

  override def att: Attributes = ???
}

case class Or(conjunctions: Set[And]) extends Proposition {
  def or(other: Or): Or =
    Or(conjunctions | other.conjunctions)

  def and(other: Or): Or = {
    Or((for (m1 <- conjunctions; m2 <- other.conjunctions) yield {
      m1 and m2
    }).flatten)
  }

  def headOption = conjunctions.headOption

  def endomap(f: And => And) = Or(conjunctions map f)

  def map[T](f: And => T) = conjunctions map f

  override def toString =
    if (conjunctions.size == 0)
      "False"
    else
      conjunctions mkString "  \\/  "

  override protected type This = this.type

  override def transform(t: PartialFunction[K, K]): K = ???

  override def copy(att: Attributes): This = ???

  override def att: Attributes = ???

  override def matchAll(k: K)(implicit rest: Theory): Or = ???
}

object Or {
  def apply(conjunctions: And*): Or = Or(conjunctions.toSet)
}

object FreeTheory extends Theory {
  /**
   * Tells whether the proposition is valid in this theory.
   * If we cannot find an answer (e.g., we have symbolic values), return None
   */
  override def apply(proposition: Proposition): Option[TruthValue] = proposition match {
    case Equals(left, right, _) => Some(if (left == right) True else False)
    case _ => None
  }
}
