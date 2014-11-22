// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import collection.{ LinearSeq, LinearSeqOptimized, Seq, generic, mutable }
import collection.JavaConverters._
import java.util.stream.StreamSupport

abstract class KList extends KListLike[KList] with Iterable[K] with KListMatcher with interfaces.KList with K with Associative {
  type ThisK = KList
  def copy(l: Iterable[K]) = KList(l.toSeq: _*)

  def ks(): java.lang.Iterable[interfaces.K] = this.asJava.asInstanceOf[java.lang.Iterable[interfaces.K]]

  override def toString = "KList(" + this.mkString(",") + ")"

  override def canEqual(that: Any) = that.isInstanceOf[KList]

  def att = Attributes()
  def copy(att: Attributes) = this
}

final case object EmptyKList extends KList with Serializable {
  override def isEmpty = true
  override def head: Nothing = throw new NoSuchElementException("head of empty klist")
  override def tail: KList = throw new UnsupportedOperationException("tail of empty klist")
  override def equals(that: Any) = canEqual(that) && (that match {
    case that: scala.collection.GenSeq[_] => that.isEmpty
    case _ => false
  })
}

final case class ConsKList(override val head: K, override val tail: KList) extends KList {
  override def isEmpty = false
  override def equals(that: Any) = canEqual(that) && (that match {
    case that: scala.collection.GenSeq[_] => !that.isEmpty && that.head == head && that.tail == tail
    case _ => false
  })
}

object KList extends CanBuildKListLike[KList] {
  def apply(l: K*): KList =
    l.foldRight(EmptyKList: KList) {
      case (h: Associative, l: KList) => KList((h ++ l).toSeq: _*)
      case (h: K, l: KList) => new ConsKList(h, l)
    }

  def fromJava(l: Array[K]) = apply(l: _*)

  def unapplySeq(l: Iterable[K]): Option[Seq[K]] = Some(l.toSeq)
}
