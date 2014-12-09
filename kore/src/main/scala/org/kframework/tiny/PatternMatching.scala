// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.tiny

import org.kframework._
import kore._
import builtin.KBoolean._
import KORE._

import scala.collection.mutable.ListBuffer

trait Pattern {
  def matchOne(k: Term): Option[Solution] = matchAll(k).headOption

  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution]
}

trait InjectedKListPattern {
  self: InjectedKList =>

  import builtin.KBoolean._
  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = ???
}

trait KListPattern extends Pattern with BindingOps {
  self: KList =>

  override def matchOne(k: Term): Option[Solution] =
    matchAllPrivate(k, true).headOption

  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] =
    matchAllPrivate(k, true)

  private def matchAllPrivate(k: Term, justOne: Boolean)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] =
    if (equiv(this, k))
      Set(Solution())
    else
      k match {
        case k: KList =>
          (k.delegate, this.delegate) match {
            case (List(), List()) => Set(Solution())
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
  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = ???
}

trait KApplyPattern extends Pattern with BindingOps {
  self: KApply =>

  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] =
    (this, k) match {
      case (KApply(labelVariable: KVariable, contentsP: Term, _), KApply(label2, contents, _)) =>
        and(Set(Solution(labelVariable -> MetaKLabel(label2))), contentsP.matchAll(contents))
      case (KApply(label, contentsP, att), KApply(label2, contents, att2)) if label == label2 =>
        contentsP.matchAll(contents)
      case (_: KApply, _) => Set()
    }
}

trait KVariablePattern extends Pattern with BindingOps {
  self: KVariable =>

  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] =
    Set(Solution(this -> k))
}

trait KRewritePattern extends Pattern with BindingOps {
  self: KRewrite =>

  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = ???
}

trait KTokenPattern extends Pattern with BindingOps {
  self: KToken =>
  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = k match {
    case KToken(`sort`, `s`, _) => Set(Solution())
    case _ => Set()
  }
}

trait KSequencePattern extends Pattern with BindingOps {
  self: KSequence =>
  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] =
    k match {
      case s: KSequence =>
        ks.matchAll(s.ks) map {
          case m: Solution => m mapValues {
            case l: KList => KSequence(l.delegate, Attributes())
            case k => k
          }
        }
    }
}

trait InjectedKLabelPattern extends Pattern {
  def matchAll(k: Term)(implicit equiv: Equivalence = EqualsEquivalence): Set[Solution] = ???
}

case class Anywhere(pattern: Term, name: String = "SINGLETON") extends K with Collection[Term] with BindingOps {
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

  def matchAll(k: Term)(implicit equiv: Equivalence): Set[Solution] = {
    val localSolution = and(pattern.matchAll(k), Set(Solution(TOPVariable -> (HOLEVariable: Term))))
    val childrenSolutions: Set[Solution] = k match {
      case kk: Collection[_] =>
        val k = kk.asInstanceOf[Collection[Term]]
        (k map { c: Term =>
          val solutions = this.matchAll(c)
          val updatedSolutions = solutions map {
            case s =>
              val newAnywhere: Term = k map { childK: Term =>
                childK match {
                  case `c` => s(TOPVariable)
                  case other: Term => other
                }
              }
              val anywhereWrapper = Solution(TOPVariable -> newAnywhere)
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
