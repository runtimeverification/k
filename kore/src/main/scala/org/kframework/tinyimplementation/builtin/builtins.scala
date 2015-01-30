// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.tinyimplementation.builtin

import org.kframework.AssocBuilder
import org.kframework.koreimplementation._
import org.kframework.tinyimplementation.TrueAndFalse._
import org.kframework.tinyimplementation._
import org.kframework.attributes._

import scala.collection.mutable.{Builder, ListBuffer}

case class KEquals(left: K, right: K, att: Attributes = Attributes()) extends KAbstractCollection with Proposition {
  type This = KEquals

  def copy(att: Attributes): KEquals = KEquals(left, right, att)

  def delegate = List(left, right)

  def matchAll(k: K, sideConditions: Proposition = True)(implicit rest: Theory): Or = {
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

  def matchAll(k: K, sideConditions: Proposition = True)(implicit rest: Theory): Or = {
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

  def matchAll(k: K, sideConditions: Proposition = True)(implicit rest: Theory): Or = {
    throw new RuntimeException("We shouldn't match directly on an OR. It must be handled by the pattern matcher separately.")
  }

  def newBuilder() = KAnd.newBuilder()
}

object KAnd {
  def newBuilder(): Builder[K, KAnd] = ListBuffer() mapResult { case List(x, y) => KAnd(x, y) }
}

case class KBoolean(v: Boolean, att: Attributes = Attributes())
  extends KToken with Proposition with Leaf {
  type This = KBoolean
  val sort = KBoolean
  val s: String = v.toString

  def copy(att: Attributes) = KBoolean(v, att)
}

object KBoolean extends Sort with KLabel {
  implicit def toKBoolean(b: Boolean): KBoolean = KBoolean(b)

  val name: String = "Boolean"
}

case class KInt(n: Int, att: Attributes = Attributes()) extends KToken with Leaf {
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
case class KBag(klabel: KLabel, val klist: KList, att: Attributes = Attributes()) extends KAbstractCollection {
  type This = KBag

  def canEqual(that: Any) = that.isInstanceOf[KBag]

  def copy(att: Attributes): KBag = this

  def newBuilder: Builder[K, KBag] = new AssocBuilder[K, List[K], KBag](ListBuffer()) mapResult { new KBag(klabel, _, att) }

  override def toString = if (isEmpty) ".Bag" else "Bag(" + mkString(",") + ")"

  override def matchAll(k: K, sideConditions: Proposition)(implicit theory: Theory): Or = k match {
    case that: KBag if that.klabel == klabel =>
      if (theory(InjectedKList(klist), InjectedKList(that.klist)))
        Or(True)
      else if (this.find(_.isInstanceOf[KVariable]) != Set())
        if (klist.size == 1 && klist.head.isInstanceOf[KVariable])
          Or((that.klist.iterable.toSeq map { Equals(klist.head, _) }): _*)
        else
          False
      else
        False
    case _ => False
  }

  override val delegate: Iterable[K] = klist.delegate
}

/*
Given an item 'foo(1, 2, 3, 4), there are several ways to match it:

1. Fixed, based on arity
'foo(X, 2, 3, 4) => X -> 1
'foo(X, 4) => None

2. Assoc
'foo(X, 2, 3, 4) => X -> 1  ..... or should it be X -> 'foo(X, .foo)?
'foo(X, 4) => X -> 'foo(1, 2, 3)
'foo(1, X, 4) => X -> 'foo(2, 3)
'foo(X, Y) => (X -> .foo && Y -> 'foo(1, 2, 3, 4)) || (X -> 1 && Y -> 'foo(2, 3, 4)) || ....

3. Assoc comm normal, without enumeration, i.e., where the order of the match doesn't matter (combinations)
'foo(X, 2, 3, 4) => X -> 1
'foo(X, 1, 2, 3) => X => 4
'foo(X, 2, 3) => X -> 'foo(1, 4)
'foo(1, X, Y) => all combinations

4. Assoc comm only arrangements, with enumeration, i.e., where the order of the match does matter (arrangements)
 */

//case class KSet(val content: Set[K]) extends KAbstractCollection with Associative[KBag] {
//  type This = KSet
//
//  def canEqual(that: Any) = that.isInstanceOf[KSet]
//  def att = Attributes()
//  def copy(att: Attributes): KSet = this
//  def matchAll(pattern: K, condition: K = KBoolean(true))(implicit rest: Disjunction = EqualsEquivalence): Set[Map[KVariable, K]] = ???
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
