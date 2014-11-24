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

case class KBag(val klist: KList) extends KAbstractCollection with Associative[KBag] {
  type This = KBag

  def canEqual(that: Any) = that.isInstanceOf[KBag]
  def att = Attributes()
  def copy(att: Attributes): KBag = this
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
