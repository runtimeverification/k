package org.kframework.tiny

import org.kframework._
import org.kframework.kore.KVariable
import org.kframework.kore.K

trait Proposition

case class Equation(left: K, right: K) extends Proposition

trait TruthValue

object True extends Conjunction(Set()) with TruthValue {
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
  def apply(propositions: Proposition*): Proposition =
    propositions.foldLeft(True: Proposition) {
    case (sum: Conjunction, c: Conjunction) => Conjunction(sum.ps | c.ps)
    case (sum: Conjunction, d: Disjunction) => Conjunction(sum.ps | c.ps)
  }

    if(propositions.exists { p => p.isInstanceOf[Disjunction] })
      propositions map {
        case d: Disjunction => d
        case p => Disjunction(p)
      }
    }
    else
        Disjunction(conjunctions.toSet)

  def and(other: Disjunction): Disjunction = {
    Disjunction(
      for (m1 <- conjunctions; m2 <- other.conjunctions) yield {
        m1 and m2
      })
  }
}

case class Conjunction(ps: Set[Equation]) extends Proposition {
  def toString = ps mkString "  /\\  "

  def and(that: Conjunction): Conjunction = Conjunction(this.ps | that.ps)
}

case class Disjunction(conjunctions: Set[Conjunction]) extends Proposition {

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
  def apply(ps: Proposition*): Disjunction =
    ps.foldLeft(False: Disjunction){
    case (d: Disjunction, p: Disjunction) => or(d, p)
    case (d: Disjunction, p: Proposition) => or(d, Disjunction(p))
  }

  def or(t: Disjunction, other: Disjunction): Disjunction =
    Disjunction(t.conjunctions | other.conjunctions)
}

object FreeTheory extends Theory {
  def apply(a: K, b: K): Boolean = a == b
}
