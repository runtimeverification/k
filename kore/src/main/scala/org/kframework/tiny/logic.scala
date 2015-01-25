package org.kframework.tiny

import org.kframework._
import org.kframework.kore._
import org.kframework.tiny.Or

import scala.collection.mutable

trait Proposition extends K {
  def and(p: Proposition): Proposition = And(this, p)

  def or(p: Proposition): Proposition = Or(this, p)
}

trait Predicate extends Proposition

trait Equals extends Proposition with Predicate {
  def left: K

  def right: K
}

object Equals {
  def apply(left: K, right: K, att: Attributes = Attributes()): Equals = (left, right) match {
    case (left: KVariable, right) => Binding(left, right, att)
    case (left, right: KVariable) => Binding(right, left, att)
    case (left, right) => SimpleEquals(right, left, att)
  }

  def unapply(e: Equals): Option[(K, K, Attributes)] = e match {
    case Binding(left, right, att) => Some(left, right, att)
    case SimpleEquals(left, right, att) => Some(left, right, att)
  }
}


case class SimpleEquals(left: K, right: K, att: Attributes = Attributes()) extends Equals {
  def matchAll(k: K)(implicit rest: Theory): Or = ???

  override type This = SimpleEquals

  override def copy(att: Attributes): This = SimpleEquals(left, right, att)

  override def transform(t: PartialFunction[K, K]): K = ???
}

case class Binding(variable: KVariable, value: K, att: Attributes = Attributes()) extends Equals {
  val left = variable
  val right = value
  override type This = Binding

  override def matchAll(k: K)(implicit rest: Theory): Or = ???

  override def copy(att: Attributes): This = Binding(variable, value, att)

  override def transform(t: PartialFunction[K, K]): K = ???
}

import TrueAndFalse._

trait Theory {
  /**
   * Tells whether the proposition is valid in this theory.
   * If we cannot find an answer (e.g., we have symbolic values), return None
   * So None means the Proposition is satisfiable.
   */
  def apply(proposition: Proposition): Option[Boolean]

  def normalize(p: Or): Or = Or((p.conjunctions map normalize).toSeq: _*)

  def normalize(p: Proposition): Proposition = p match {
    case p: Or => normalize(p)
    case p: Proposition => apply(p) map toProposition getOrElse p
  }

  /**
   * Helper method
   */
  def apply(left: K, right: K): Boolean = apply(Equals(left, right)) == Some(True)
}

case class PropositionTheory(p: Proposition) extends Theory {
  def apply(proposition: Proposition): Option[Boolean] = (proposition and p) match {
    case True => Some(true)
    case False => Some(false)
    case sum => FreeTheory.apply(sum)
  }
}

object And {
  def apply(propositions: Proposition*): Proposition =
    propositions.fold(True: Proposition) {
      case (True, p: And) => p
      case (True, Binding(k, v, _)) => new And(Set(), Map(k -> v))
      case (True, p: Predicate) => new And(Set(p), Map())
      case (sum: Proposition, True) => sum
      case (sum: Proposition, False) => False
      case (False, p: Proposition) => False

      case (sum: And, p: And) => sum andOption p getOrElse False
      case (sum: And, p: Or) =>
        Or((for (m1 <- p.conjunctions) yield {
          m1 and sum
        }).toSeq: _*)

      case (sum: Or, p: And) => And(p, sum)
      case (sum: Or, p: Or) =>
        Or((for (m1 <- sum.conjunctions; m2 <- p.conjunctions) yield {
          m1 and m2
        }).toSeq: _*)
      case (sum: And, Binding(k, v, _)) => (sum andOption new And(Set[Predicate](), Map(k -> v))) getOrElse False
      case (sum: And, p: Predicate) => new And(sum.predicates + p, sum.bindings)
      case (sum: Or, p: Predicate) => And(sum, And(p))
    }

  def unapplySeq(and: And): Option[Seq[Predicate]] =
    Some(and.predicates.toSeq ++ (and.bindings map { case (k, v) => Binding(k, v) }))
}

case class And(predicates: Set[Predicate], bindings: Map[KVariable, K]) extends Proposition {

  def andOption(that: And): Option[And] = {
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
  def or(other: Or): Or = Or(this, other)


  def and(other: Or): Or = Or(And(this, other))

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
  def apply(propositions: Proposition*): Or =
    propositions.foldLeft(False: Or) {
      case (sum: Or, True) => new Or(Set(True))
      case (or, p: Proposition) if or.conjunctions.contains(True) => new Or(Set(True))
      case (sum: Or, False) => sum

      case (sum: Or, p: Or) => new Or(sum.conjunctions | p.conjunctions)
      case (sum: Or, p: And) => new Or(sum.conjunctions + p)
      case (sum: Or, p: Predicate) => new Or(sum.conjunctions + And(p).asInstanceOf[And])
    }

  def unapplySeq(or: Or): Option[Seq[And]] = Some(or.conjunctions.toSeq)
}

object FreeTheory extends Theory {
  /**
   * Tells whether the proposition is valid in this theory.
   * If we cannot find an answer (e.g., we have symbolic values), return None
   */
  override def apply(proposition: Proposition): Option[Boolean] = proposition match {
    case Equals(left, right, _) => Some(left == right)
    case _ => None
  }
}

object TrueAndFalse {
  val True = new And(Set(), Map())
  val False = new Or(Set())

  implicit def toProposition(x: Boolean) = x match {
    case true => True
    case false => False
  }

  implicit def pairToBinding(p: (KVariable, K)) = Binding(p._1, p._2)
}