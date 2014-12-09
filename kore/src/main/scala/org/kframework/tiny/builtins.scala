// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.tiny.builtin

import org.kframework._
import kore._
import KORE._
import scala.collection.mutable.Builder
import scala.collection.mutable.SetBuilder
import org.kframework.tiny.Equivalence
import org.kframework.tiny.EqualsEquivalence
import org.kframework.tiny._
import Pattern._
import collection.mutable.ListBuffer

trait Proposition

case class KEquals(left: K, right: K, att: Attributes = Attributes()) extends KAbstractCollection with Proposition {
  type This = KEquals
  def copy(att: Attributes): KEquals = KEquals(left, right, att)
  def delegate = List(left, right)

  def matchAll(k: Term)(implicit equiv: Equivalence): Set[Solution] = {
    throw new RuntimeException("We shouldn't match directly on an equals. It must be handled by the pattern matcher separately.")
  }
  def newBuilder() = KEquals.newBuilder()
}

object KEquals {
  def newBuilder(): Builder[K, KEquals] = ListBuffer() mapResult { case List(x, y) => KEquals(x, y) }
}

case class KOr(left: K, right: K, att: Attributes = Attributes()) extends KAbstractCollection with Proposition {
  type This = KOr
  def copy(att: Attributes): KOr = KOr(left, right, att)
  def delegate = List(left, right)

  def matchAll(k: Term)(implicit equiv: Equivalence): Set[Solution] = {
    throw new RuntimeException("We shouldn't match directly on an OR. It must be handled by the pattern matcher separately.")
  }
  def newBuilder() = KOr.newBuilder()
}

object KOr {
  def newBuilder(): Builder[K, KOr] = ListBuffer() mapResult { case List(x, y) => KOr(x, y) }
}

case class KAnd(left: K, right: K, att: Attributes = Attributes()) extends KAbstractCollection with Proposition {
  type This = KAnd
  def copy(att: Attributes): KAnd = KAnd(left, right, att)
  def delegate = List(left, right)

  def matchAll(k: Term)(implicit equiv: Equivalence): Set[Solution] = {
    throw new RuntimeException("We shouldn't match directly on an OR. It must be handled by the pattern matcher separately.")
  }
  def newBuilder() = KAnd.newBuilder()
}

object KAnd {
  def newBuilder(): Builder[K, KAnd] = ListBuffer() mapResult { case List(x, y) => KAnd(x, y) }
}

case class KBoolean(v: Boolean, att: Attributes = Attributes()) extends KToken with Proposition {
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
//
//case class KString(s: String, att: Attributes = Attributes()) extends KToken {
//  type This = KString
//  val sort = KString
//  def copy(att: Attributes) = KString(s, att)
//}
//
//object KString extends Sort with KLabel {
//  implicit def toKString(s: String): KString = KString(s)
//
//  val name: String = "Int"
//}
//
//case class KBag(val klist: KList) extends KAbstractCollection with Associative[KBag] {
//  type This = KBag
//
//  def canEqual(that: Any) = that.isInstanceOf[KBag]
//  def att = Attributes()
//  def copy(att: Attributes): KBag = this
//  def matchAll(pattern: Term, condition: Term = KBoolean(true))(implicit equiv: Equivalence = EqualsEquivalence): Set[Map[KVariable, Term]] = ???
//
//  val delegate = klist.delegate
//  def newBuilder: Builder[K, KBag] = KBag.newBuilder
//
//  override def toString = if (isEmpty) ".Bag" else "Bag(" + mkString(",") + ")"
//}
//
//object KBag extends Sort with KLabel {
//  def newBuilder = KList.newBuilder() mapResult { new KBag(_) }
//
//  val name: String = "Bag"
//}
//
//case class KSet(val content: Set[K]) extends KAbstractCollection with Associative[KBag] {
//  type This = KSet
//
//  def canEqual(that: Any) = that.isInstanceOf[KSet]
//  def att = Attributes()
//  def copy(att: Attributes): KSet = this
//  def matchAll(pattern: Term, condition: Term = KBoolean(true))(implicit equiv: Equivalence = EqualsEquivalence): Set[Map[KVariable, Term]] = ???
//
//  val delegate = content
//  def newBuilder: Builder[K, KSet] = KSet.newBuilder
//
//  override def toString = if (isEmpty) ".Set" else "Set(" + mkString(",") + ")"
//}
//
//object KSet {
//  def newBuilder: Builder[K, KSet] = new SetBuilder[K, Set[K]](Set[K]()) mapResult { new KSet(_) }
//  def apply(ks: K*): KSet = (newBuilder ++= ks).result
//}
//
//
////case class ScalaObject(pckage: String, name: String) extends KLabel {
////  def fullName = pckage + "." + name
////}
////
////object ScalaObject {
////  def apply(fullName: String): ScalaObject = {
////    val r = fullName.split(".").reverse
////    ScalaObject(r.tail.reverse.mkString("."), r.head)
////  }
////}
