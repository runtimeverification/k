package org.kframework.kore

import org.kframework._

import KBoolean._
import KORE._

case class MatchException(m: String) extends RuntimeException(m)

object Pattern {
  type Solution = Map[KVariable, K]
}

import Pattern.Solution

trait Pattern {
  def matchOne(k: K, condition: K = true): Option[Map[KVariable, K]] = matchAll(k, condition).headOption

  def matchAll(k: K, condition: K = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution]
}

trait BindingOps {

  def or(s1: Set[Solution], s2: Set[Solution]): Set[Solution] =
    s1 | s2

  def and(s1: Set[Solution], s2: Set[Solution]): Set[Solution] = {
    (for (m1 <- s1; m2 <- s2) yield {
      and(m1, m2)
    }).flatten
  }

  def and(m1: Map[KVariable, K], m2: Map[KVariable, K]): Option[Map[KVariable, K]] = {
    //  if variables are bound to distinct terms, m1 and m2 is false (none)
    if ((m1.keys.toSet & m2.keys.toSet).exists(v => m1(v) != m2(v))) {
      None
    } else
      Some(m1 ++ m2)
  }
}

trait Equivalence {
  def apply(a: K, b: K): Boolean
}

object EqualsEquivalence extends Equivalence {
  def apply(a: K, b: K): Boolean = a == b
}

trait PatternByReflection {
  self: { def productIterator: Iterable[K] } =>
  def matchAll(k: K, condition: K = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = {
    ???
  }
}

trait KListPattern extends Pattern with BindingOps {
  self: KList =>

  def matchAll(k: K, condition: K = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] =
    if (equiv(this, k))
      Set(Map())
    else
      k match {
        case k: KList =>
          (k.delegate, this.delegate) match {
            case (List(), List()) => Set(Map())
            case (head +: tail, headP +: tailP) if equiv(headP, head) => tailP.matchAll(tail)
            case (_, (v: KVariable) +: tailP) =>
              (0 to k.size)
                .map { index => (k.delegate.take(index), k.delegate.drop(index)) }
                .map {
                  case (prefix, suffix) =>
                    and(Set(Map(v -> (prefix: K))), tailP.matchAll(suffix))
                }
                .fold(Set())(or)
            case _ => Set()
          }
      }
}

case class MetaKLabel(klabel: KLabel) extends KItem {
  type This = MetaKLabel
  def copy(att: Attributes) = this
  def att = Attributes()
  def matchAll(k: K, condition: K = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = ???
}

trait KApplyPattern extends Pattern with BindingOps {
  self: KApply =>

  def matchAll(k: K, condition: K = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] =
    (this, k) match {
      case (KApply(labelVariable: KVariable, contentsP: K, att), KApply(label2, contents, att2)) =>
        and(Set(Map(labelVariable -> MetaKLabel(label2))), contentsP.matchAll(contents, condition))
      case (KApply(label, contentsP, att), KApply(label2, contents, att2)) if label == label2 =>
        contentsP.matchAll(contents, condition)
      case (_: KApply, _) => Set()
    }
}

trait KVariablePattern extends Pattern with BindingOps {
  self: KVariable =>

  def matchAll(k: K, condition: K = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] =
    Set(Map(this -> k))
}

trait KRewritePattern extends Pattern with BindingOps {
  self: KRewrite =>

  def matchAll(k: K, condition: K = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = ???
}

trait KTokenPattern extends Pattern with BindingOps {
  self: KToken =>
  def matchAll(k: K, condition: K = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = k match {
    case KToken(`sort`, `s`, _) => Set(Map())
    case _ => Set()
  }
}

trait KSequencePattern extends Pattern with BindingOps {
  self: KSequence =>
  def matchAll(k: K, condition: K = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] =
    k match {
      case s: KSequence =>
        ks.matchAll(s.ks, condition) map {
          case m: Map[_, _] => m.asInstanceOf[Map[KVariable, KList]] mapValues { l => KSequence(l.delegate, Attributes()) }
        }
    }
}
