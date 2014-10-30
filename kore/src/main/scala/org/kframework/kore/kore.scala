// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import collection.JavaConverters._
import collection.LinearSeq
import KORE._

/* Interfaces */

sealed trait KORE // marker for KORE final classes added as a result of a discussion with Brandon about sealing

trait HasAttributes {
  def att: Attributes
}

trait K extends HasAttributes {
  protected type Self <: K

  def copy(att: Attributes): Self
  def copy(): Self = copy(att)
}

trait KItem extends K

trait KLabel // needs to be a KLabel to be able to have KVariables in its place

trait KCollection[+This <: KCollection[This]] extends K with GenericCollection[K, This] with HasAttributes {
  self: This =>
  def copy(att: Attributes) = copy(KList(), att)
  def copy(klist: KList, att: Attributes): This
  def copy(klist: KList): This = copy(klist, att)
  def copy(klist: LinearSeq[K]): This = copy(new KList(klist), att)
  def klist: KList
  protected val items = klist
}

/* Data Structures */

final class Attributes(val items: LinearSeq[K]) extends GenericCollection[K, Attributes] {
  // we will eventually decide on something much more specific for attributes
  def copy(klist: LinearSeq[K]) = new Attributes(klist)
}

final class KList(val items: LinearSeq[K]) extends GenericCollection[K, KList] with KORE {
  def copy(klist: LinearSeq[K]) = new KList(items)
}

case class KString(s: String) // just a wrapper to mark it

case class KApply(klabel: KLabel, klist: KList, att: Attributes = Attributes()) extends KCollection[KApply] with KORE {
  def copy(klist: KList, att: Attributes) = KApply(klabel, klist, att)
}

case class KToken(sort: Sort, s: KString, att: Attributes = Attributes()) extends KItem with KORE {
  type Self = KToken
  def copy(att: Attributes): KToken = new KToken(sort, s, att)
}

case class ConcreteKLabel(name: String) extends KLabel {
  def apply(ks: K*) = KApply(this, KList(ks: _*))
}

final class KSequence(val klist: KList, val att: Attributes = Attributes()) extends KCollection[KSequence] {
  def copy(klist: KList, att: Attributes): KSequence = KSequence(klist, att)
}

case class KVariable(name: String, att: Attributes = Attributes()) extends KItem with KORE {
  type Self = KVariable
  def copy(att: Attributes): KVariable = new KVariable(name, att)
}

case class KRewrite(left: K, right: K, att: Attributes = Attributes()) extends KCollection[KRewrite] with KORE {
  def copy(klist: KList, att: Attributes): KRewrite = KRewrite(klist, att)
  val klist = KList(left, right)
}

/*  Constructors */

object KVariable {
  val it = this
}

object Attributes {
  def apply(klist: KList): Attributes = new Attributes(klist)
  def apply(): Attributes = new Attributes(KList())
}

object KList extends CanBuildGeneric[K, KList] {
  def apply(l: K*) = new KList(l.toList)
  implicit def inject(k: K): KList = KList(k)

  def fromJava(l: Array[K]) = new KList(l.toList)
}

object KSequence extends CanBuild[KSequence] {
  def apply(klist: KList, att: Attributes) = new KSequence(klist, att)

  def fromJava(l: Array[K]) = new KSequence(new KList(l.toList), Attributes())
}

object EmptyK {
  def apply() = KSequence()
}

object KRewrite extends CanBuild[KRewrite] {
  def apply(klist: KList, att: Attributes) = klist match {
    case Seq(left, right) => new KRewrite(left, right, att)
  }
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

object EmptyKList {
  def apply() = List[K]()
}

case class Sort(name: String)

/* Implicits for nicer Scala interfaces */

object KCollection {
  type T = KCollection[T] forSome { type T <: KCollection[T] }

  import collection._

  implicit def canBuildFrom: generic.CanBuildFrom[T, K, T] =
    new generic.CanBuildFrom[T, K, T] {
      def apply(): mutable.Builder[K, T] = ??? // we have no truly generic K collection -- hm... we might consider KList to the that
      def apply(from: T): mutable.Builder[K, T] = GenericCollection.newBuilder(l => from.copy(new KList(l)))
    }
}

object KORE {
  implicit def StringToKString(s: String) = KString(s)
}
