package org.kframework.kore

import org.kframework._
import KBoolean._
import KORE._

import Pattern.Solution
import scala.collection.mutable.ListBuffer

case class MatchException(m: String) extends RuntimeException(m)

object Pattern {
  type Solution = Map[KVariable, Term]
}

trait Pattern {
  def matchOne(k: Term, condition: Term = true): Option[Map[KVariable, Term]] = matchAll(k, condition).headOption

  def matchAll(k: Term, condition: Term = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution]
}

trait BindingOps {

  def or(s1: Set[Solution], s2: Set[Solution]): Set[Solution] =
    s1 | s2

  def and(s1: Set[Solution], s2: Set[Solution]): Set[Solution] = {
    (for (m1 <- s1; m2 <- s2) yield {
      and(m1, m2)
    }).flatten
  }

  def and(m1: Map[KVariable, Term], m2: Map[KVariable, Term]): Option[Map[KVariable, Term]] = {
    //  if variables are bound to distinct terms, m1 and m2 is false (none)
    if ((m1.keys.toSet & m2.keys.toSet).exists(v => m1(v) != m2(v))) {
      None
    } else
      Some(m1 ++ m2)
  }
}

trait Equivalence {
  def apply(a: Term, b: Term): Boolean
}

object EqualsEquivalence extends Equivalence {
  def apply(a: Term, b: Term): Boolean = a == b
}

trait PatternByReflection {
  self: { def productIterator: Iterable[Term] } =>
  def matchAll(k: Term, condition: Term = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = {
    ???
  }
}

trait KListPattern extends Pattern with BindingOps {
  self: KList =>

  def matchAll(k: Term, condition: Term = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] =
    if (equiv(this, k))
      Set(Map())
    else
      k match {
        case k: KList =>
          (k.delegate, this.delegate) match {
            case (List(), List()) => Set(Map())
            //            case (head +: tail, headP +: tailP) if equiv(headP, head) => tailP.matchAll(tail)
            case (_, headP +: tailP) =>
              (0 to k.size)
                .map { index => (k.delegate.take(index), k.delegate.drop(index)) }
                .map {
                  case (List(oneElement), suffix) =>
                    and(headP.matchAll(oneElement), tailP.matchAll(suffix))
                  case (prefix, suffix) =>
                    and(headP.matchAll(prefix), tailP.matchAll(suffix))
                }
                .fold(Set())(or)
            case other => Set()
          }
      }
}

case class MetaKLabel(klabel: KLabel) extends KItem {
  type This = MetaKLabel
  def copy(att: Attributes) = this
  def att = Attributes()
  def matchAll(k: Term, condition: Term = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = ???
}

trait KApplyPattern extends Pattern with BindingOps {
  self: KApply =>

  def matchAll(k: Term, condition: Term = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] =
    (this, k) match {
      case (KApply(labelVariable: KVariable, contentsP: Term, _), KApply(label2, contents, _)) =>
        and(Set(Map(labelVariable -> MetaKLabel(label2))), contentsP.matchAll(contents, condition))
      case (KApply(label, contentsP, att), KApply(label2, contents, att2)) if label == label2 =>
        contentsP.matchAll(contents, condition)
      case (_: KApply, _) => Set()
    }
}

trait KVariablePattern extends Pattern with BindingOps {
  self: KVariable =>

  def matchAll(k: Term, condition: Term = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] =
    Set(Map(this -> k))
}

trait KRewritePattern extends Pattern with BindingOps {
  self: KRewrite =>

  def matchAll(k: Term, condition: Term = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = ???
}

trait KTokenPattern extends Pattern with BindingOps {
  self: KToken =>
  def matchAll(k: Term, condition: Term = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = k match {
    case KToken(`sort`, `s`, _) => Set(Map())
    case _ => Set()
  }
}

trait KSequencePattern extends Pattern with BindingOps {
  self: KSequence =>
  def matchAll(k: Term, condition: Term = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] =
    k match {
      case s: KSequence =>
        ks.matchAll(s.ks, condition) map {
          case m: Map[_, _] => m.asInstanceOf[Map[KVariable, Term]] mapValues {
            case l: KList => KSequence(l.delegate, Attributes())
            case k => k
          }
        }
    }
}

trait InjectedKLabelPattern extends Pattern {
  def matchAll(k: Term, condition: Term = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = ???
}

case class Anywhere(pattern: Term) extends Collection[Term] with BindingOps {
  type This = Anywhere

  def delegate = List(pattern)
  def att = Attributes()
  def copy(att: Attributes) = this

  def newBuilder = ListBuffer() mapResult {
    case List(x) => Anywhere(x)
    case _ => throw new UnsupportedOperationException()
  }
  import Anywhere._

  def matchAll(k: Term, condition: Term)(implicit equiv: Equivalence): Set[Pattern.Solution] = {
    val localSolution = and(pattern.matchAll(k), Set(Map(TOP -> (HOLE: Term))))
    val childrenSolutions = k match {
      case k: Collection[Term] =>
        (k map { c: Term =>
          val solutions = this.matchAll(c)
          val updatedSolutions = solutions map {
            case s =>
              val newAnywhere: Term = k map { childK: Term =>
                childK match {
                  case `c` => s(TOP)
                  case other: Term => other
                }
              }
              val anywhereWrapper = Map(TOP -> newAnywhere)
              s ++ anywhereWrapper
          }
          updatedSolutions
        }).fold(Set())(or)
      case _ => Set[Solution]()
    }
    or(localSolution, childrenSolutions)
  }

  def foreach(f: Term => Unit): Unit = delegate foreach f
  def iterable: Iterable[Term] = delegate
}

object Anywhere {
  val TOP = KVariable("TOP")
  val HOLE = KVariable("HOLE")
}