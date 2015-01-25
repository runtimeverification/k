// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.tiny

import org.kframework._
import kore._
import builtin.KBoolean._
import KORE._

import scala.collection.mutable.ListBuffer

trait Pattern {
  def matchOne(k: K)(implicit theory: Theory): Option[K] = matchAll(k).headOption

  def matchAll(k: K)(implicit rest: Theory): Disjunction
}

trait InjectedKListPattern {
  self: InjectedKList =>

  import builtin.KBoolean._
  def matchAll(k: K)(implicit rest: Theory): Disjunction = ???
}

trait KListPattern {
  self: KList =>

  def matchOne(klist: KList)(implicit rest: Theory): Option[K] =
    matchAllPrivate(klist, true).headOption

  def matchAll(klist: KList)(implicit rest: Theory): Disjunction =
    matchAllPrivate(klist, true)

  private def matchAllPrivate(klist: KList, justOne: Boolean)(implicit rest: Theory): Disjunction = {
    if (!this.delegate.zipAll(klist.delegate, KSequence(), KSequence())
      .exists({ case (a, b) => !rest(a, b) }))
      Disjunction(True)
    else
      (klist.delegate, this.delegate) match {
        case (List(), List()) => Disjunction(True)
        case (head +: tail, headP +: tailP) if rest(headP, head) => tailP.matchAll(tail)
        case (_, headP +: tailP) =>
          (0 to klist.size)
            .map { index => (klist.delegate.take(index), klist.delegate.drop(index)) }
            .map {
              case (List(oneElement), suffix) =>
                headP.matchAll(oneElement) and tailP.matchAll(suffix)
              case (prefix, suffix) =>
                headP.matchAll(InjectedKList(prefix)) and tailP.matchAll(suffix)
            }
            .fold(False)({ (a, b) => a or b })
        case other => False
      }
  }
}

case class MetaKLabel(klabel: KLabel) extends KItem with Leaf {
  type This = MetaKLabel
  def copy(att: Attributes) = this
  def att = Attributes()
  def matchAll(k: K)(implicit rest: Theory): Disjunction = ???
}

trait KApplyPattern extends Pattern {
  self: KApply =>

  def matchAll(k: K)(implicit rest: Theory): Disjunction = {
    (this, k) match {
      case (KApply(labelVariable: KVariable, contentsP, _), KApply(label2, contents, _)) =>
        Disjunction(Conjunction(labelVariable -> MetaKLabel(label2))) and contentsP.matchAll(contents)
      case (KApply(label, contentsP, att), KApply(label2, contents, att2)) if label == label2 =>
        contentsP.matchAll(contents)
      case (_: KApply, _) => False
    }
  }
}

trait KVariablePattern extends Pattern {
  self: KVariable =>

  def matchAll(k: K)(implicit rest: Theory): Disjunction = {
    Disjunction(Conjunction(this -> k))
  }
}

trait KRewritePattern extends Pattern {
  self: KRewrite =>

  def matchAll(k: K)(implicit rest: Theory): Disjunction = ???
}

trait KTokenPattern extends Pattern {
  self: KToken =>
  def matchAll(k: K)(implicit rest: Theory): Disjunction = {
    k match {
      case KToken(`sort`, `s`, _) => Disjunction(True)
      case _ => False
    }
  }
}

trait KSequencePattern extends Pattern {
  self: KSequence =>
  def matchAll(k: K)(implicit rest: Theory): Disjunction =
    k match {
      case s: KSequence =>
        ks.matchAll(s.ks) endomap {
          case m: Conjunction => m mapValues {
            case InjectedKList(l, _) => KSequence(l.delegate, Attributes())
            case k => k
          }
        }
    }
}

trait InjectedKLabelPattern extends Pattern {
  def matchAll(k: K)(implicit rest: Theory): Disjunction = ???
}

case class Anywhere(pattern: K, name: String = "SINGLETON") extends K with KCollection {
  type This = Anywhere

  def delegate = List(pattern)
  def att = Attributes()
  def copy(att: Attributes) = Anywhere(pattern, name)

  def newBuilder = ListBuffer() mapResult {
    case List(x) => Anywhere(x)
    case _ => throw new UnsupportedOperationException()
  }
  import Anywhere._

  val TOPVariable = KVariable("TOP_" + name)
  val HOLEVariable = KVariable("HOLE_" + name)

  def matchAll(k: K)(implicit rest: Theory): Disjunction = {
    val localSolution = pattern.matchAll(k) and Disjunction(Conjunction(TOPVariable -> (HOLEVariable: K)))
    val childrenSolutions: Disjunction = k match {
      case k: KCollection =>
        (k map { c: K =>
          val solutions = this.matchAll(c)
          val updatedSolutions = solutions endomap {
            case s =>
              val newAnywhere: K = k map { childK: K =>
                childK match {
                  case `c` => s(TOPVariable)
                  case rest: K => rest
                }
              }
              val anywhereWrapper = TOPVariable -> newAnywhere
              Conjunction(s.propositions, s.bindings + anywhereWrapper)
          }
          updatedSolutions
        }).fold(Disjunction())((a, b) => a or b)
      case _ => False
    }
    localSolution or childrenSolutions
  }

  def foreach(f: K => Unit): Unit = delegate foreach f
  def iterable: Iterable[K] = delegate
}
