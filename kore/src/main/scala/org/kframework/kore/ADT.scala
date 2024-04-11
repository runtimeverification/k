// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kore

import org.kframework.attributes._
import org.kframework.builtin.KLabels
import org.kframework.builtin.Sorts
import org.kframework.kore
import scala.jdk.CollectionConverters._

/**
 * Abstract Data Types: basic implementations for the inner KORE interfaces.
 *
 * Tools using inner KORE data structures can either use these classes directly or have their own
 * implementations.
 */

object ADT {

  case class KLabel(name: String, params: kore.Sort*) extends kore.KLabel {
    override def toString =
      if (params.isEmpty) {
        name
      } else {
        name + "{" + params.map(_.toString).reduce((s1, s2) => s1 + "," + s2) + "}"
      }
  }

  case class KApply[KK <: K](klabel: kore.KLabel, klist: kore.KList, att: Att = Att.empty)
      extends kore.KApply {
    def items      = klist.items
    def size       = klist.size
    def asIterable = klist.asIterable
  }

  class KSequence private (val elements: List[K], val att: Att = Att.empty) extends kore.KSequence {
    val items: java.util.List[K]          = elements.asJava
    val size: Int                         = elements.size
    val asIterable: java.lang.Iterable[K] = new org.kframework.List(elements)
    lazy val kApply: kore.KApply =
      items.asScala.reduceRightOption((a, b) => KLabels.KSEQ.apply(a, b)).getOrElse {
        KLabels.DOTK.apply()
      } match {
        case k: kore.KApply => k
        case x              => KLabels.KSEQ(x, KLabels.DOTK())
      }

    def iterator: Iterator[K] = elements.iterator

    override def equals(that: Any) = that match {
      case s: KSequence => s.elements == elements
      case _            => false
    }
  }

  object KSequence {
    private val emptyAtt = Att.empty

    def raw(elements: scala.collection.immutable.List[K]): KSequence =
      new KSequence(elements, emptyAtt)

    def apply(elements: List[K], att: Att = Att.empty): KSequence =
      new KSequence(
        elements.foldLeft(List[K]()) {
          case (sum, s: KSequence) => sum ++ s.items.asScala
          case (sum, t)            => sum :+ t
        },
        att
      )
  }

  case class KVariable(name: String, att: Att = Att.empty) extends kore.KVariable {}

  case class Sort(name: String, params: kore.Sort*) extends kore.Sort {
    override def toString =
      if (params.isEmpty) {
        name
      } else {
        name + "{" + params.map(_.toString).reduce((s1, s2) => s1 + "," + s2) + "}"
      }
  }

  case class SortHead(name: String, params: Int) extends kore.SortHead {
    override def toString =
      if (params == 0) {
        name
      } else {
        name + "{" + (0 until params).map("S" + _.toString).reduce((s1, s2) => s1 + "," + s2) + "}"
      }
  }
  case class KToken(s: String, sort: kore.Sort, att: Att = Att.empty) extends kore.KToken

  case class KList(elements: List[K]) extends kore.KList {
    lazy val items: java.util.List[K] = elements.asJava
    def iterator: Iterator[K]         = elements.iterator
    lazy val size                     = elements.size
    lazy val asIterable               = new org.kframework.List(elements)
  }

  case class KRewrite(left: kore.K, right: kore.K, att: Att = Att.empty) extends kore.KRewrite

  case class KAs(pattern: kore.K, alias: kore.K, att: Att = Att.empty) extends kore.KAs

  case class InjectedKLabel(klabel: kore.KLabel, att: Att) extends kore.InjectedKLabel

}

object SortedADT {

  case class SortedKVariable(name: String, att: Att = Att.empty) extends kore.KVariable {
    val sort: Sort =
      if (att.contains(Att.CELL_SORT)) Sorts.K
      else
        att
          .getOptional(Att.SORT, classOf[Sort])
          .orElse(Sorts.K)

    override def equals(other: Any) = other match {
      case v: SortedKVariable => name == v.name && sort == v.sort
      // case v: KVariable => throw new UnsupportedOperationException(s"should not mix
      // SortedKVariables with KVariables for variable $this and $v")
      case _ => false
    }
  }

}
