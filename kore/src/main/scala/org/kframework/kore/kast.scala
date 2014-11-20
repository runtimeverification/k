// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import collection.JavaConverters._
import collection.LinearSeq
import KORE._
import scala.collection.AbstractIterator
import scala.collection.IterableLike
import scala.collection.generic.CanBuildFrom

/* Interfaces */

trait KCollection extends Iterable[K] with Matcher {
  type ThisK
  def copy(klist: Iterable[K]): ThisK
}

sealed trait KORE // marker for KORE final classes added as a result of a discussion with Brandon about sealing

trait HasAttributes {
  def att: Attributes
}

trait K extends HasAttributes with Matcher with Rewriting {
  protected type ThisK <: K

  def copy(att: Attributes): ThisK
  def copy(): ThisK = copy(att)
}

trait KItem extends K

trait KLabel extends KLabelToString {
  val name: String
} // needs to be a KLabel to be able to have KVariables in its place

/* Data Structures */

case class KString(s: String) // just a wrapper to mark it

case class KApply(klabel: KLabel, klist: KCollection, att: Attributes = Attributes())
  extends KAbstractCollection[KApply] with KORE with KApplyMatcher with KApplyToString {
  type ThisK = KApply
  def copy(klist: KCollection, att: Attributes): KApply = new KApply(klabel, klist, att)

  override def equals(that: Any) = that match {
    case KApply(`klabel`, _, _) => super.equals(that)
    case _ => false
  }
}

trait KToken extends KItem with KORE with KTokenMatcher {
  val sort: Sort
  val s: KString
}

case class KUninterpretedToken(sort: Sort, s: KString, override val att: Attributes = Attributes())
  extends KToken with KTokenToString {
  type ThisK = KToken
  def copy(att: Attributes): KToken = new KUninterpretedToken(sort, s, att)
}

case class ConcreteKLabel(name: String) extends KLabel {
  def apply(ks: K*) = KApply(this, KList(ks: _*))
}

final class KSequence(val klist: KList, val att: Attributes = Attributes())
  extends KAbstractCollection[KSequence] with KSequenceMatcher {
  self: KSequence =>
  type ThisK = KSequence
  def copy(klist: KCollection, att: Attributes): KSequence = new KSequence(KList(klist.toSeq: _*), att)

  override def map(f: java.util.function.Function[K, K]): KSequence = {
    val builder = newBuilder
    foreach {
      builder += f(_)
    }
    builder.result()
  }
}

case class KVariable(name: String, att: Attributes = Attributes())
  extends KItem with KORE with KLabel with KVariableMatcher {
  type ThisK = KVariable
  def copy(att: Attributes): KVariable = new KVariable(name, att)
}

case class KRewrite(left: K, right: K, att: Attributes = Attributes())
  extends K with KORE with KRewriteMatcher with KRewriteToString {
  self: KRewrite =>
  type ThisK = KRewrite
  def copy(att: Attributes): KRewrite = new KRewrite(left, right, att)
  val klist = KList(left, right)
}

/*  Constructors */

object KToken {
  def apply(sort: Sort, s: KString, att: Attributes = Attributes()) =
    KUninterpretedToken(sort, s, att)

  def unapply(t: KToken) = Some((t.sort, t.s, t.att))
}

object KVariable {
  val it = this
}

object KSequence extends CanBuildKListLike[KSequence] {
  def apply(klist: KList, att: Attributes) = new KSequence(klist, att)
  def apply(list: K*) = apply(list, Attributes())

  def fromJava(l: Array[K]) = new KSequence(KList(l: _*), Attributes())
}

object KRewrite {
  def apply(klist: KList, att: Attributes): KRewrite = klist match {
    case KList(left, right) => new KRewrite(left, right, att)
  }
  def apply(list: K*): KRewrite = apply(list, Attributes())
}

object KApply extends CanBuildKListLike[KApply] {
  def apply(list: K*) = throw new UnsupportedOperationException("Cannot create a KApply from just a list of Ks. It also needs a KLabel")
}

object EmptyK {
  def apply() = KSequence(KList(), Attributes())
}

object KLabel {
  def apply(name: String) = ConcreteKLabel(name)
  def unapply(klabel: ConcreteKLabel): Option[String] = Some(klabel.name)
}

/* Constructors for matching KORE */

object KLabelWithQuotes {
  def apply(s: String) = {
    KLabel(s.stripPrefix("`").stripSuffix("`"))
  }
}

case class Sort(name: String) extends SortToString

object KORE {
  implicit def StringToKString(s: String) = KString(s)

  implicit def seqOfKsToKList(ks: Seq[K]) = KList(ks: _*)

  implicit def SymbolToKLabel(s: Symbol) = KLabel(s.name)
}
