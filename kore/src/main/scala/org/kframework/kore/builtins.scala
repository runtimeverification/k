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

object KBoolean extends Sort with KLabel {
  implicit def toKBoolean(b: Boolean): KBoolean = KBoolean(b)
  val name: String = "Boolean"
}

case class KInt(n: Int, att: Attributes = Attributes()) extends KToken {
  type This = KInt
  val sort = KInt
  val s: KString = n.toString
  def copy(att: Attributes) = KInt(n, att)
}

object KInt extends Sort with KLabel {
  implicit def toKInt(n: Int): KInt = KInt(n)

  val name: String = "Int"
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

object KBag extends Sort with KLabel {
  def newBuilder = KList.newBuilder mapResult { new KBag(_) }

  val name: String = "Bag"
}

case object Hole extends KLabel with Sort {
  val name = "HOLE"
}
