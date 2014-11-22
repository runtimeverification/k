// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import KORE._
import KBoolean._

case class KBoolean(v: Boolean, att: Attributes = Attributes()) extends KToken {
  type ThisK = KBoolean
  val sort = KBoolean
  val s: KString = v.toString

  def copy(att: Attributes) = KBoolean(v, att)
}

object KBoolean extends Sort("Boolean") {
  implicit def toKBoolean(b: Boolean): KBoolean = b match {
    case true => KBoolean(true)
    case false => KBoolean(false)
  }
}

object KInt {
  object KInt extends Sort("Boolean")

  case class KInt(n: Int, att: Attributes = Attributes()) extends KToken {
    type ThisK = KInt
    val sort = KInt
    val s: KString = n.toString
    def copy(att: Attributes) = KInt(n, att)
  }

  implicit def toKInt(n: Int): KInt = KInt(n)
}

class KSet(private val backingSet: Set[K]) extends collection.AbstractSet[K] with Associative[KSet] {
  type ThisK = KSet

  def contains(key: K): Boolean = backingSet.contains(key)
  def iterator: Iterator[K] = backingSet.iterator
  def +(elem: K): KSet = new KSet(backingSet + elem)
  def -(elem: K): KSet = new KSet(backingSet - elem)

  def matchAll(pattern: K, condition: K = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Map[KVariable, K]] = ???

  def copy(l: Iterable[K]): KSet = new KSet(l.toSet)
  def copy(att: Attributes) = this
  def att = Attributes()
}

class KBag(val contents: KList) extends KAbstractCollection[KBag] with Associative[KBag] {
  type ThisK = KBag

  def att = Attributes()
  def copy(klist: Iterable[K], att: Attributes): KBag = new KBag(KList(klist.toSeq: _*))
  def matchAll(pattern: K, condition: K = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Map[KVariable, K]] = ???

  override def newBuilder: collection.mutable.Builder[K, KBag] =
    contents.newBuilder mapResult copy
}

object KBag extends ConcreteKLabel("Bag")

object Hole extends ConcreteKLabel("Hole")
