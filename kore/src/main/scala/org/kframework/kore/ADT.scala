package org.kframework.kore

import org.kframework.builtin.KLabels
import org.kframework.kore
import org.kframework.attributes._
import collection.JavaConverters._

/**
 * Abstract Data Types: basic implementations for the inner KORE interfaces.
 *
 * Tools using inner KORE data structures can either use these classes directly or have their own implementations.
 */


object ADT {

  case class KLabel(name: String) extends kore.KLabel {
    override def toString = name

    def apply(ks: K*) = KApply(this, KList(ks.toList))
  }

  case class KApply[KK <: K](klabel: kore.KLabel, klist: kore.KList, att: Att = Att()) extends kore.KApply {
    def items = klist.items
  }

  class KSequence private(val elements: List[K], val att: Att = Att()) extends kore.KSequence {
    val items: java.util.List[K] = elements.asJava
    val kApply: kore.KApply = items.asScala reduceRightOption { (a, b) => KLabel(KLabels.KSEQ)(a, b) } getOrElse { KLabel(KLabels.DOTK)() } match {
      case k: kore.KApply => k
      case x => KLabel(KLabels.KSEQ)(x, KLabel(KLabels.DOTK)())
    }

    def iterator: Iterator[K] = elements.iterator

    override def equals(that: Any) = that match {
      case s: KSequence => s.elements == elements
      case _ => false
    }
  }

  object KSequence {
    def apply(elements: List[K], att: Att = Att()): KSequence =
      new KSequence(elements.foldLeft(List[K]()) {
        case (sum, s: KSequence) => sum ++ s.items.asScala
        case (sum, t) => sum :+ t
      }, att)
  }

  case class KVariable(name: String, att: Att = Att()) extends kore.KVariable {
    def apply(ks: K*) = KApply(this, KList(ks.toList))
  }

  case class Sort(name: String) extends kore.Sort {
    override def toString = name
  }

  case class KToken(s: String, sort: kore.Sort, att: Att = Att()) extends kore.KToken

  case class KList(elements: List[K]) extends kore.KList {
    elements foreach { e => assert(e.isInstanceOf[K]) }
    def items: java.util.List[K] = elements.asJava
    def iterator: Iterator[K] = elements.iterator
  }

  case class KRewrite(left: kore.K, right: kore.K, att: Att = Att()) extends kore.KRewrite

  case class InjectedKLabel(klabel: kore.KLabel, att: Att) extends kore.InjectedKLabel

}

object SortedADT {

  case class SortedKVariable(name: String, att: Att = Att()) extends kore.KVariable {
    def apply(ks: K*) = ADT.KApply(this, ADT.KList(ks.toList))

    val sort: Sort = ADT.Sort(att.getOptional[String]("sort").orElse("K"))

    override def equals(other: Any) = other match {
      case v: SortedKVariable => name == v.name && sort == v.sort
//      case v: KVariable => throw new UnsupportedOperationException(s"should not mix SortedKVariables with KVariables for variable $this and $v")
      case _ => false
    }
  }

}