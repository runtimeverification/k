// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.builtin

import org.kframework._
import kore._
import KORE._
import scala.collection.mutable.Builder
import scala.collection.mutable.SetBuilder
import org.kframework.tiny.Equivalence
import org.kframework.tiny.EqualsEquivalence

case class KBoolean(v: Boolean, att: Attributes = Attributes()) extends KToken {
  type This = KBoolean
  val sort = KBoolean
  val s: String = v.toString

  def copy(att: Attributes) = KBoolean(v, att)
}

object KBoolean extends Sort with KLabel {
  implicit def toKBoolean(b: Boolean): KBoolean = KBoolean(b)
  val name: String = "Boolean"
}

case class KInt(n: Int, att: Attributes = Attributes()) extends KToken {
  type This = KInt
  val sort = KInt
  val s: String = n.toString
  def copy(att: Attributes) = KInt(n, att)
}

object KInt extends Sort with KLabel {
  implicit def toKInt(n: Int): KInt = KInt(n)

  val name: String = "Int"
}

case class KString(s: String, att: Attributes = Attributes()) extends KToken {
  type This = KString
  val sort = KString
  def copy(att: Attributes) = KString(s, att)
}

object KString extends Sort with KLabel {
  implicit def toKString(s: String): KString = KString(s)

  val name: String = "Int"
}

case class KBag(val klist: KList) extends KAbstractCollection with Associative[KBag] {
  type This = KBag

  def canEqual(that: Any) = that.isInstanceOf[KBag]
  def att = Attributes()
  def copy(att: Attributes): KBag = this
  def matchAll(pattern: Term, condition: Term = KBoolean(true))(implicit equiv: Equivalence = EqualsEquivalence): Set[Map[KVariable, Term]] = ???

  val delegate = klist.delegate
  def newBuilder: Builder[K, KBag] = KBag.newBuilder

  override def toString = if (isEmpty) ".Bag" else "Bag(" + mkString(",") + ")"
}

object KBag extends Sort with KLabel {
  def newBuilder = KList.newBuilder() mapResult { new KBag(_) }

  val name: String = "Bag"
}

case class KSet(val content: Set[K]) extends KAbstractCollection with Associative[KBag] {
  type This = KSet

  def canEqual(that: Any) = that.isInstanceOf[KSet]
  def att = Attributes()
  def copy(att: Attributes): KSet = this
  def matchAll(pattern: Term, condition: Term = KBoolean(true))(implicit equiv: Equivalence = EqualsEquivalence): Set[Map[KVariable, Term]] = ???

  val delegate = content
  def newBuilder: Builder[K, KSet] = KSet.newBuilder

  override def toString = if (isEmpty) ".Set" else "Set(" + mkString(",") + ")"
}

object KSet {
  def newBuilder: Builder[K, KSet] = new SetBuilder[K, Set[K]](Set[K]()) mapResult { new KSet(_) }
  def apply(ks: K*): KSet = (newBuilder ++= ks).result
}

object Location {
  import KInt._

  def apply(startLine: Int, startColumn: Int, endLine: Int, endColumn: Int) = {
    'location('startLine(startLine), 'startColumn(startColumn), 'endLine(endLine), 'endColumn(endColumn))
  }
}
