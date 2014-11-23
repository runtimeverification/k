// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import collection.JavaConverters._
import collection.LinearSeq
import KORE._
import scala.collection.AbstractIterator
import scala.collection.IterableLike
import scala.collection.generic.CanBuildFrom
import scala.collection.mutable.Builder

/* Interfaces */

sealed trait KORE // marker for KORE final classes added as a result of a discussion with Brandon about sealing

trait HasAttributes {
  def att: Attributes
}

trait K extends HasAttributes with Matcher with Rewriting with interfaces.K {
  protected type ThisK <: K

  def copy(att: Attributes): ThisK
}

trait KItem extends K with interfaces.KItem {
  //  def ~>(seq: KSequence): KSequence = this +: seq 
}

trait KLabel extends KLabelToString with interfaces.KLabel {
  val name: String
} // needs to be a KLabel to be able to have KVariables in its place

/* Data Structures */

case class KString(s: String) extends interfaces.KString // just a wrapper to mark it

class KApply(val klabel: KLabel, val contents: KList, val att: Attributes = Attributes())
  extends KAbstractCollection[KApply] with KORE with KApplyMatcher with KApplyToString with Equals {
  type ThisK = KApply

  override def canEqual(that: Any) = that match {
    case t: KApply => t.klabel == klabel
    case _ => false
  }

  def copy(ks: Iterable[K], att: Attributes): KApply = KApply(klabel, ks, att)
}

trait KToken extends KItem with KORE with KTokenMatcher with KTokenToString with interfaces.KToken {
  val sort: Sort
  val s: KString
}

case class KUninterpretedToken(sort: Sort, s: KString, override val att: Attributes = Attributes())
  extends KToken with KTokenToString {
  type ThisK = KToken
  def copy(att: Attributes): KToken = new KUninterpretedToken(sort, s, att)
}

case class ConcreteKLabel(name: String) extends KLabel {
  def apply(ks: K*) = KApply(this, ks)
}

final class KSequence(val contents: KList, val att: Attributes = Attributes())
  extends KAbstractCollection[KSequence] with KSequenceMatcher with KSequenceToString {
  self: KSequence =>
  type ThisK = KSequence
  def copy(klist: Iterable[K], att: Attributes): KSequence = new KSequence(KList(klist.toSeq: _*), att)
  def klist = KList(contents.toSeq: _*)

  override def canEqual(that: Any) = that.isInstanceOf[KSequence]
}

case class KVariable(name: String, att: Attributes = Attributes())
  extends KItem with KORE with KLabel with KVariableMatcher with KVariableToString {
  type ThisK = KVariable
  def copy(att: Attributes): KVariable = new KVariable(name, att)
}

case class KRewrite(left: K, right: K, att: Attributes = Attributes())
  extends K with KORE with KRewriteMatcher with KRewriteToString with interfaces.KRewrite {
  self: KRewrite =>
  type ThisK = KRewrite
  def copy(att: Attributes): KRewrite = new KRewrite(left, right, att)
  val klist = KList(left, right)
}

/*  Constructors */

object KApply {
  def apply(klabel: KLabel, contents: Iterable[K], att: Attributes = Attributes()) = {
    new KApply(klabel, KList(contents), att)
  }

  def unapply(a: KApply): Option[(KLabel, KList, Attributes)] = Some((a.klabel, a.contents, a.att))
}

object KToken {
  def apply(sort: Sort, s: KString, att: Attributes = Attributes()) =
    KUninterpretedToken(sort, s, att)

  def unapply(t: KToken) = Some((t.sort, t.s, t.att))
}

object KVariable {
  val it = this
}

object KSequence extends CanBuildKCollection[KSequence] {
  def apply(klist: KList, att: Attributes) = new KSequence(klist, att)
  def apply(list: K*) = apply(KList(list: _*), Attributes())

  def fromJava(l: Array[K]) = new KSequence(KList(l: _*), Attributes())
}

object KRewrite {
  def apply(klist: KList, att: Attributes): KRewrite = klist match {
    case KList(left, right) => new KRewrite(left, right, att)
  }
  def apply(list: K*): KRewrite = apply(KList(list: _*), Attributes())
}

object EmptyK {
  def apply() = KSequence(KList(), Attributes())
}

object KLabel extends ConcreteKLabel("KLabel") {
  def apply(name: String) = ConcreteKLabel(name)
  def unapply(klabel: ConcreteKLabel): Option[String] = Some(klabel.name)
}

/* Constructors for matching KORE */

object KLabelWithQuotes {
  def apply(s: String) = {
    KLabel(s.stripPrefix("`").stripSuffix("`"))
  }
}

case class Sort(name: String) extends SortToString with interfaces.Sort

object KORE {
  implicit def StringToKString(s: String) = KString(s)

  implicit def seqOfKsToKList(ks: Seq[K]) = KList(ks: _*)

  implicit def SymbolToKLabel(s: Symbol) = KLabel(s.name)
}
