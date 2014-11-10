// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import collection.{ AbstractSeq, LinearSeq, LinearSeqOptimized, Seq, generic, mutable }

trait Context

trait KCollection[+This <: KCollection[This]]
  extends KListBacked[This] with K {
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

  def copy(klist: KList, att: Attributes): ThisK
  def copy(klist: LinearSeq[K]): ThisK = copy(klist, att)

  override def foreach[B](f: K => B) {
    klist.foreach(f)
  }
}

trait AttributesToString {
  self: Attributes =>
  override def toString() = "[" +
    (klist map {
      case KApply(KLabel(keyName), KList(KToken(_, KString(value), _)), _) => keyName + "(" + value + ")"
    } mkString " ") + "]"

  def postfixString = if (isEmpty) "" else (" " + toString())

  def map(f: java.util.function.Function[K, K]): This = {
    val builder = newBuilder
    foreach {
      builder += f(_)
    }
    builder.result()
  }
}

trait SortToString {
  self: Sort =>
  override def toString = name
}
