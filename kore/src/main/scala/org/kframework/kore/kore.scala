// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import collection.JavaConverters._
import collection.LinearSeq
import KORE._
import scala.collection.AbstractIterator
import scala.collection.IterableLike
import scala.collection.generic.CanBuildFrom

/* Interfaces */

sealed trait KORE // marker for KORE final classes added as a result of a discussion with Brandon about sealing

trait HasAttributes {
  def att: Attributes
}

trait K extends HasAttributes {
  protected type ThisK <: K

  def copy(att: Attributes): ThisK
  def copy(): ThisK = copy(att)
}

trait KItem extends K

trait KLabel // needs to be a KLabel to be able to have KVariables in its place

/* Data Structures */

final class Attributes(val klist: KList) extends KListBacked[Attributes] {
  import KList.seqOfKtoKList
  // we will eventually decide on something much more specific for attributes
  def copy(klist: LinearSeq[K]) = new Attributes(klist)
}

case class KString(s: String) // just a wrapper to mark it

case class KApply(klabel: KLabel, klist: KList, att: Attributes = Attributes()) extends KCollection[KApply] with KORE {
  type ThisK = KApply
  def copy(klist: KList, att: Attributes) = new KApply(klabel, klist, att)

  // Java interop until Scala-2.12
  def map(f: java.util.function.Function[K, K]): KApply = map(e => f(e))
}

case class KToken(sort: Sort, s: KString, att: Attributes = Attributes()) extends KItem with KORE {
  type ThisK = KToken
  def copy(att: Attributes): KToken = new KToken(sort, s, att)
}

case class ConcreteKLabel(name: String) extends KLabel {
  def apply(ks: K*) = KApply(this, KList(ks: _*))
}

final class KSequence(val klist: KList, val att: Attributes = Attributes()) extends KCollection[KSequence] {
  self: KSequence =>
  type ThisK = KSequence
  def copy(klist: KList, att: Attributes): KSequence = new KSequence(klist, att)

  // Java interop until Scala-2.12
  def map(f: java.util.function.Function[K, K]): KSequence = map(e => f(e))
}

case class KVariable(name: String, att: Attributes = Attributes()) extends KItem with KORE {
  type ThisK = KVariable
  def copy(att: Attributes): KVariable = new KVariable(name, att)
}

case class KRewrite(left: K, right: K, att: Attributes = Attributes()) extends KCollection[KRewrite] with KORE {
  self: KRewrite =>
  type ThisK = KRewrite
  def copy(l: KList, att: Attributes): KRewrite = l match {
    case KList(left, right) => new KRewrite(left, right, att)
  }
  val klist = KList(left, right)

  // Java interop until Scala-2.12
  def map(f: java.util.function.Function[K, K]): KRewrite = map(e => f(e))
}

/*  Constructors */

object KVariable {
  val it = this
}

object Attributes extends CanBuildKListLike[Attributes] {
  def apply(klist: KList): Attributes = new Attributes(klist)
  def apply(list: K*): Attributes = new Attributes(list)
}

object KSequence extends CanBuildKListLike[KSequence] {
  def apply(klist: KList, att: Attributes) = new KSequence(klist, att)
  def apply(list: K*) = apply(list, Attributes())

  def fromJava(l: Array[K]) = new KSequence(KList(l: _*), Attributes())
}

object KRewrite extends CanBuildKListLike[KRewrite] {
  def apply(klist: KList, att: Attributes) = klist match {
    case KList(left, right) => new KRewrite(left, right, att)
  }
  def apply(list: K*) = apply(list, Attributes())
}

object KApply extends CanBuildKListLike[KApply] {
  def apply(list: K*) = throw new UnsupportedOperationException("Cannot create a KApply from just a list of Ks. It also needs a KLabel")
}

object EmptyK {
  def apply() = KSequence(KList(), Attributes())
}

object KLabel {
  def apply(name: String) = ConcreteKLabel(name)
}

/* Constructors for matching KORE */

object KLabelWithQuotes {
  def apply(s: String) = {
    KLabel(s.stripPrefix("`").stripSuffix("`"))
  }
}

case class Sort(name: String)

object KORE {
  implicit def StringToKString(s: String) = KString(s)
}
