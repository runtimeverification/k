// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.tiny

import org.kframework._
import kore._
import builtin.KBoolean._
import KORE._

import scala.collection.mutable.ListBuffer

trait Pattern {
  def matchOne(k: Term): Option[Conjunction] = matchAll(k).headOption

  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Disjunction
}

trait InjectedKListPattern {
  self: InjectedKList =>

  import builtin.KBoolean._
  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Disjunction = ???
}

trait KListPattern extends Pattern {
  self: KList =>

  override def matchOne(k: Term): Option[Conjunction] =
    matchAllPrivate(k, true).headOption

  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Disjunction =
    matchAllPrivate(k, true)

  private def matchAllPrivate(k: Term, justOne: Boolean)(implicit equiv: Equivalence = EqualsEquivalence): Disjunction =
    if (equiv(this, k))
      Disjunction(Conjunction())
    else
      k match {
        case k: KList =>
          (k.delegate, this.delegate) match {
            case (List(), List()) => Disjunction(Conjunction())
            case (head +: tail, headP +: tailP) if equiv(headP, head) => tailP.matchAll(tail)
            case (_, headP +: tailP) =>
              (0 to k.size)
                .map { index => (k.delegate.take(index), k.delegate.drop(index)) }
                .map {
                  case (List(oneElement), suffix) =>
                    headP.matchAll(oneElement) and tailP.matchAll(suffix)
                  case (prefix, suffix) =>
                    headP.matchAll(prefix) and tailP.matchAll(suffix)
                }
                .fold(Disjunction())({ (a, b) => a or b })
            case other => Disjunction()
          }
      }
}

case class MetaKLabel(klabel: KLabel) extends KItem {
  type This = MetaKLabel
  def copy(att: Attributes) = this
  def att = Attributes()
  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Disjunction = ???
}

trait KApplyPattern extends Pattern {
  self: KApply =>

  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Disjunction =
    (this, k) match {
      case (KApply(labelVariable: KVariable, contentsP: Term, _), KApply(label2, contents, _)) =>
        Disjunction(Conjunction(labelVariable -> MetaKLabel(label2))) and contentsP.matchAll(contents)
      case (KApply(label, contentsP, att), KApply(label2, contents, att2)) if label == label2 =>
        contentsP.matchAll(contents)
      case (_: KApply, _) => Disjunction()
    }
}

trait KVariablePattern extends Pattern {
  self: KVariable =>

  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Disjunction =
    Disjunction(Conjunction(this -> k))
}

trait KRewritePattern extends Pattern {
  self: KRewrite =>

  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Disjunction = ???
}

trait KTokenPattern extends Pattern {
  self: KToken =>
  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Disjunction = {
    k match {
      case KToken(`sort`, `s`, _) => Disjunction(Conjunction())
      case _ => Disjunction()
    }
  }
}

trait KSequencePattern extends Pattern {
  self: KSequence =>
  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Disjunction =
    k match {
      case s: KSequence =>
        ks.matchAll(s.ks) endomap {
          case m: Conjunction => m mapValues {
            case l: KList => KSequence(l.delegate, Attributes())
            case k => k
          }
        }
    }
}

trait InjectedKLabelPattern extends Pattern {
  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Disjunction = ???
}

case class Anywhere(pattern: Term, name: String = "SINGLETON") extends K with Collection[Term] {
  type This = Anywhere

  def delegate = List(pattern)
  def att = Attributes()
  def copy(att: Attributes) = this

  def newBuilder = ListBuffer() mapResult {
    case List(x) => Anywhere(x)
    case _ => throw new UnsupportedOperationException()
  }
  import Anywhere._

  val TOPVariable = KVariable("TOP_" + name)
  val HOLEVariable = KVariable("HOLE_" + name)

  def matchAll(k: Term)(implicit equiv: Equivalence): Disjunction = {
    val localSolution = pattern.matchAll(k) and Disjunction(Conjunction(TOPVariable -> (HOLEVariable: Term)))
    val childrenSolutions: Disjunction = k match {
      case kk: Collection[_] =>
        val k = kk.asInstanceOf[Collection[Term]]
        (k map { c: Term =>
          val solutions = this.matchAll(c)
          val updatedSolutions = solutions endomap {
            case s =>
              val newAnywhere: Term = k map { childK: Term =>
                childK match {
                  case `c` => s(TOPVariable)
                  case other: Term => other
                }
              }
              val anywhereWrapper = Conjunction(TOPVariable -> newAnywhere)
              s ++ anywhereWrapper
          }
          updatedSolutions
        }).fold(Disjunction())((a, b) => a or b)
      case _ => Disjunction()
    }
    localSolution or childrenSolutions
  }

  def foreach(f: Term => Unit): Unit = delegate foreach f
  def iterable: Iterable[Term] = delegate
}
