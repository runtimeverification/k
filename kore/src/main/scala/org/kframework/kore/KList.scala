// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import collection.{ LinearSeq, LinearSeqOptimized, Seq, generic, mutable }
import collection.JavaConverters._
import java.util.stream.StreamSupport
import scala.collection.mutable.Builder

class KList(val delegate: List[K]) extends KAbstractCollection with KListMatcher with K with Associative[KList] {
  type This = KList
  def copy(l: Iterable[K], att: Attributes) = KList(l.toSeq: _*)

  override def toString = "KList(" + this.mkString(",") + ")"
  override def canEqual(that: Any) = that.isInstanceOf[KList]
  override def newBuilder: Builder[K, KList] = KList.newBuilder

  def att = Attributes()

  //FIXME: when Scala 2.12 is out
  def map(f: java.util.function.Function[K, K]): KList = map(f(_))

  def copy(att: Attributes): KList = this
}

object KList extends CanBuildKCollection {
  type This = KList

  def apply(l: Iterable[K]): KList = (newBuilder ++= l).result()

  def newBuilder: Builder[K, KList] =
    new AssocBuilder[K, KList] mapResult { new KList(_) }

  def unapplySeq(l: KList): Option[Seq[K]] = Some(l.delegate.toSeq)
}
