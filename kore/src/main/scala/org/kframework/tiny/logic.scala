package org.kframework.tiny

import org.kframework._
import org.kframework.kore.KVariable
import org.kframework.kore.K

trait Proposition
trait Predicate

trait Equation extends Proposition with Predicate {
  def left: K
  def right: K
}

case class Equals(left: K, right: K) extends Equation

case class Binding(v: KVariable, t: K) extends Equation

trait TruthValue

object True extends Conjunction(Set(), Bindings()) with TruthValue {
  def toString = "True"
}
object False extends Disjunction(Set()) with TruthValue {
  def toString = "False"
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
    base.apply(Conjunction(proposition, extra))
  }
}

object Bindings {
  def apply(pairs: (KVariable, K)*): Bindings = Bindings(pairs.toMap)
}

case class Bindings(bindings: Map[KVariable, K]) extends Proposition {
  def apply(v: KVariable) = bindings(v)
  def mapValues(f: K => K) = Bindings(bindings mapValues f)
  def contains(v: KVariable) = bindings contains v

  def ++(other: Bindings) = Bindings(bindings ++ other.bindings)
  def +(other: (KVariable, K)) = Bindings(bindings + other)

  def and(that: Bindings): Option[Bindings] = {
    //  if variables are bound to distinct terms, m1 and m2 is false (none)
    if ((bindings.keys.toSet & that.bindings.keys.toSet).exists(v => bindings(v) != that.bindings(v))) {
      None
    } else
      Some(this ++ that)
  }

  override def toString =
    if (bindings.size == 0)
      "True"
    else
      bindings map { case (k, v) => k + "=" + v } mkString "  /\\  "
}

object Conjunction {
  def apply(propositions: Proposition*): Conjunction =
    propositions.foldLeft(True: Conjunction) {
      case (sum: Conjunction, c: Conjunction) => Conjunction(sum, c)
      case (sum: Conjunction, e: Predicate) => Conjunction(sum.ps + Disjunction(Set(e)), sum.bindings)
      case (sum: Conjunction, d: Disjunction) => Conjunction(sum.ps + d, sum.bindings)
    }

  def apply(a: Conjunction, b: Conjunction): Conjunction = {
    val newBindings = a.bindings and b.bindings
    newBindings map { Conjunction(a.ps | b.ps, _) } getOrElse Conjunction(False)
  }
}

case class Conjunction(ps: Set[Disjunction], bindings: Bindings) extends Proposition {
  def toString = ps mkString "  /\\  "
}

case class Disjunction(ps: Set[Predicate]) extends Proposition {

  def headOption = ps.headOption

  def endomap(f: Predicate => Predicate) = Disjunction(ps map f)

  def map[T](f: Predicate => T) = ps map f

  override def toString =
    if (ps.size == 0)
      "False"
    else
      ps mkString "  \\/  "
}

object Disjunction {
  def apply(ps: Proposition*): Proposition =
    ps.foldLeft(False: Proposition) {
      case (sum: Disjunction, p: Predicate) => Disjunction(sum.ps + p)
      case (sum: Disjunction, d: Disjunction) => Disjunction(sum.ps | d.ps)
      case (sum: Disjunction, c: Conjunction) => or(Conjunction(sum), c)
      case (sum: Conjunction, c: Conjunction) => or(sum, c)
      case (sum: Conjunction, c: Disjunction) => or(sum, Conjunction(c))
    }

  def or(a: Conjunction, b: Conjunction): Conjunction = {
    (a.bindings and b.bindings)
      .map { bindings =>
        Conjunction((for (m1 <- a.ps; m2 <- b.ps) yield {
          Disjunction(m1, m2).asInstanceOf[Disjunction]
        }), bindings)
      }
      .getOrElse(Conjunction(False))
  }
}

object FreeTheory extends Theory {
  def apply(a: K, b: K): Boolean = a == b
}
