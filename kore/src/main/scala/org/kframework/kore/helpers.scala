// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import collection.{ AbstractSeq, LinearSeq, LinearSeqOptimized, Seq, generic, mutable }

trait Context

trait KAbstractCollection[+This <: KAbstractCollection[This]]
  extends KListBacked[This] with KCollection with K {
  self: This =>
  type ThisK <: This

  override def toString() = super.toString() + " copy " + att
  override def equals(that: Any) = that match {
    case that: This => that.klist.equals(this.klist) && that.att.equals(this.att)
    case _ => false
  }

  def copy(a: Attributes): ThisK = {
    copy(klist, att ++ a)
  }

  def copy(klist: KCollection, att: Attributes): ThisK
  def copy(klist: Iterable[K]): ThisK = copy(KList(klist.toSeq: _*), att)

  override def foreach[B](f: K => B) {
    klist.foreach(f)
  }

  def map(f: java.util.function.Function[K, K]): This = {
    val builder = newBuilder
    foreach {
      builder += f(_)
    }
    builder.result()
  }
}

trait AttributesToString {
  self: Attributes =>

  override def toString() = "[" +
    (klist map {
      case KApply(KLabel(keyName), KList(KToken(_, KString(value), _)), _) => keyName + "(" + value + ")"
    } mkString " ") + "]"

  def postfixString = if (isEmpty) "" else (" " + toString())
}

trait SortToString {
  self: Sort =>
  override def toString = name
}
