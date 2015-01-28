package org.kframework.tiny

import org.kframework.kore._
import org.kframework.tiny.TrueAndFalse._

import scala.collection.mutable

trait Proposition extends K {
  def and(p: Proposition)(implicit theory: Theory): Proposition = And(this, p)

  def or(p: Proposition)(implicit theory: Theory): Proposition = Or(this, p)
}

trait Predicate extends Proposition

trait Equals extends Proposition with Predicate {
  def left: K

  def right: K
}

object Equals {
  def apply(left: K, right: K, att: Attributes = Attributes()): Equals = (left, right) match {
    // case (left: KVariable, right: KVariable) => throw new UnsupportedOperationException("We do not support direct equality of variables yet.")
    case (left: KVariable, right) if right.find(x => x.isInstanceOf[KVariable]) == Set() => Binding(left, right, att)
    case (left, right: KVariable) if !left.isInstanceOf[KVariable] => apply(left, right, att)
    case (left, right) => SimpleEquals(right, left, att)
  }

  def unapply(e: Equals): Option[(K, K, Attributes)] = e match {
    case Binding(left, right, att) => Some(left, right, att)
    case SimpleEquals(left, right, att) => Some(left, right, att)
  }
}


case class SimpleEquals(left: K, right: K, att: Attributes = Attributes()) extends SimpleCaseClass with Equals {
  def matchAll(k: K)(implicit rest: Theory): Or = ???

  override type This = SimpleEquals

  override def copy(att: Attributes): This = SimpleEquals(left, right, att)

  override def matchAll(k: K, sideConditions: Proposition)(implicit theory: Theory): Or = ???
}

case class Binding(variable: KVariable, value: K, att: Attributes = Attributes()) extends Equals {
  val left = variable
  val right = value
  override type This = Binding

  override def matchAll(k: K, sideConditions: Proposition = True)(implicit rest: Theory): Or = ???

  override def copy(att: Attributes): This = Binding(variable, value, att)

  override def transform(t: PartialFunction[K, K]): K = ???

  override def find(f: (K) => Boolean): Set[K] = ???
}

import org.kframework.tiny.TrueAndFalse._

trait Theory {

  implicit val thisIsImplicit = this

  /**
   * Tells whether the proposition is valid in this theory.
   * If we cannot find an answer (e.g., we have symbolic values), return None
   * So None means the Proposition is satisfiable.
   */
  def apply(proposition: Proposition): Option[Boolean]

  def normalize(or: Or): Or = {
    val normalizedConjunctions = or.conjunctions.map(normalize(_))

    if (normalizedConjunctions.contains(True))
      Or(True)
    else {
      val notted: Set[Predicate] = or.conjunctions.collect {
        case and: And if and.predicates.size == 1 && and.predicates.head.isInstanceOf[Not] =>
          and.head.asInstanceOf[Not].predicate
      }
      if (or.conjunctions.exists(_.predicates == notted))
        Or(True)
      else {
        val noFalse = normalizedConjunctions.filterNot { _ == False }
        for (p <- noFalse) {assert(p.isInstanceOf[And]) }
        Or(noFalse.asInstanceOf[Set[And]])
      }
    }
  }

  def normalize(and: And): Proposition = {
    //            apply(and) map toProposition getOrElse and
    val newPredicates: Set[Predicate] =
      and.predicates
        .map { p => apply(p) map toProposition getOrElse p }
        .filterNot { _ == True }
        .asInstanceOf[Set[Predicate]]

    val nots: Set[Predicate] = newPredicates.filter({ case p: Not => true; case _ => false }).toSet
    if (!(newPredicates & nots).isEmpty) // a and !a = False TODO: make it use the equiv from the theory
      False
    else if (newPredicates.exists(_ == False) || apply(True) == Some(false)) // a and False = False
      False
    else
      And(newPredicates, and.bindings)
  }

  def normalize(p: Proposition): Proposition = p match {
    case p: Or => normalize(p)
    case p: And => normalize(p)
  }

  /**
   * Helper method; Returns true when left == right
   */
  def apply(left: K, right: K): Boolean = apply(Equals(left, right)) == Some(True)
}

case class PropositionTheory(p: Proposition) extends Theory {
  def apply(entailed: Proposition): Option[Boolean] =
    FreeTheory.normalize((entailed and p) or Not(p)) match {
    case True => Some(true)
    case False => Some(false)
    case sum => FreeTheory.apply(sum)
  }
}

object Not {
  def apply(proposition: Proposition)(implicit theory: Theory): Proposition = proposition match {
    case or: Or => And(or.conjunctions map { Not(_) } toSeq: _*)
    case and: And => Or(and.predicates map { Not(_) } toSeq: _*)
    case p: Predicate => new Not(p)
  }
}

case class Not(predicate: Predicate, att: Attributes = Attributes()) extends Predicate with SimpleCaseClass {
  override type This = Not

  override def copy(att: Attributes): This = Not(predicate, att)

  override def matchAll(k: K, sideConditions: Proposition)(implicit theory: Theory): Or = ???
}

object And {
  def apply(propositions: Proposition*)(implicit theory: Theory): Proposition =
    propositions.fold(True: Proposition) {
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
      case (sum: And, Binding(k, v, _)) =>
        (sum andOption new And(Set[Predicate](), Map(k -> v))) getOrElse False
      case (sum: And, p: Predicate) => new And(sum.predicates + p, sum.bindings)
      case (sum: Or, p: Predicate) => And(sum, And(p))
    }

  def unapplySeq(and: And): Option[Seq[Predicate]] =
    Some(and.predicates.toSeq ++ (and.bindings map { case (k, v) => Binding(k, v) }))
}

case class And(predicates: Set[Predicate], bindings: Map[KVariable, K], att: Attributes = Attributes()) extends KAbstractCollection with Proposition {

  // invariant: a bound KVariable will not appear in predicates
  for (p <- predicates;
       v <- bindings.keys) {
    assert(p.find(_ == v) == Set())
  }

  def andOption(that: And)(implicit theory: Theory): Option[And] = {
    def clashingBindings(v: KVariable): Boolean =
      !theory(bindings(v), that.bindings(v))

    //  if variables are bound to distinct terms, m1 and m2 is false (none)
    if ((bindings.keys.toSet & that.bindings.keys.toSet).exists(clashingBindings)) {
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

  override type This = And

  override def delegate: Iterable[K] = predicates ++ bindings.keys ++ bindings.values

  override def copy(att: Attributes): This = ???

  override def matchAll(k: K, sideConditions: Proposition = True)(implicit theory: Theory): Or = ???

  override def newBuilder(): mutable.Builder[K, This] = ???
}

case class Or(conjunctions: Set[And], att: Attributes = Attributes()) extends KAbstractCollection with Proposition {
  def or(other: Or)(implicit theory: Theory): Or = Or(this, other)


  def and(other: Or)(implicit theory: Theory): Or = Or(And(this, other))

  def headOption = conjunctions.headOption

  def endomap(f: And => And) = Or(conjunctions map f)

  def map[T](f: And => T) = conjunctions map f

  override def toString =
    if (conjunctions.size == 0)
      "False"
    else
      conjunctions mkString "  \\/  "

  override type This = Or

  override def delegate: Iterable[K] = conjunctions

  override def copy(att: Attributes): This = ???

  override def matchAll(k: K, sideConditions: Proposition = True)(implicit theory: Theory): Or = ???

  override def newBuilder(): mutable.Builder[K, This] = ???
}

object Or {
  def apply(propositions: Proposition*)(implicit theory: Theory): Or =
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