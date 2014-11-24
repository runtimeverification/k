// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import KORE._
import KBoolean._
import scala.collection.mutable.Builder

case class KBoolean(v: Boolean, att: Attributes = Attributes()) extends KToken {
  type This = KBoolean
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

case class KInt(n: Int, att: Attributes = Attributes()) extends KToken {
  type This = KInt
  val sort = KInt
  val s: KString = n.toString
  def copy(att: Attributes) = KInt(n, att)
}

object KInt extends Sort("Boolean") {
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

case class KBag(val klist: KList) extends KAbstractCollection with Associative[KBag] {
  type This = KBag

  def canEqual(that: Any) = that.isInstanceOf[KBag]
  def att = Attributes()
  def copy(klist: Iterable[K], att: Attributes): KBag = (newBuilder ++= klist).result
  def matchAll(pattern: K, condition: K = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Map[KVariable, K]] = ???

  val delegate = klist.delegate
  def newBuilder: Builder[K, KBag] = KBag.newBuilder

  override def toString = if (isEmpty) ".Bag" else "Bag(" + mkString(",") + ")"
}

object KBag extends ConcreteKLabel("Bag") {
  def newBuilder = KList.newBuilder mapResult { new KBag(_) }
}

object Hole extends ConcreteKLabel("Hole")

object StringSort extends Sort("String")

//case class KWithCondition(t: K, condition: K) extends K {
//  type ThisK = KWithCondition
//  def att() = Attributes()
//  def copy(att: Attributes) = this
//
//  def matchAll(pattern: K, condition: K = true)(implicit equiv: Equivalence = EqualsEquivalence): Set[Map[KVariable, K]] = ???
//
//  override def toString = "#WithCondition(" + t + "," + condition + ")";
//}
