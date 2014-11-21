// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import KORE._

object KBoolean {
  object KBoolean extends Sort("Boolean")

  case class KBoolean(v: Boolean, att: Attributes = Attributes()) extends KToken {
    type ThisK = KBoolean
    val sort = KBoolean
    val s: KString = v.toString

    def copy(att: Attributes) = KBoolean(v, att)
  }

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

class KSet(private val backingSet: Set[K]) extends collection.AbstractSet[K] with KCollection {
  type ThisK = KSet

  def contains(key: K): Boolean = backingSet.contains(key)
  def iterator: Iterator[K] = backingSet.iterator
  def +(elem: K): KSet = new KSet(backingSet + elem)
  def -(elem: K): KSet = new KSet(backingSet - elem)

  def matchAll(pattern: K, condition: K)(implicit equiv: Equivalence = EqualsEquivalence): Set[Map[KVariable, K]] = ???

  def copy(l: Iterable[K]): KSet = new KSet(l.toSet)
  def copy(att: Attributes) = this
  def att = Attributes()
}
