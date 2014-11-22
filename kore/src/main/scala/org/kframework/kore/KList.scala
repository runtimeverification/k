// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import collection.{ LinearSeq, LinearSeqOptimized, Seq, generic, mutable }
import collection.JavaConverters._
import java.util.stream.StreamSupport
import scala.collection.mutable.Builder

class KList(val contents: List[K]) extends LinearSeq[K] with LinearSeqOptimized[K, KList] with KCollection[KList] with KListMatcher with K with Associative[KList] {
  type ThisK = KList
  def copy(l: Iterable[K], att: Attributes) = KList(l.toSeq: _*)
  def copy(l: List[K]) = new KList(l)

  //  def ks(): java.lang.Iterable[interfaces.K] = this.asJava.asInstanceOf[java.lang.Iterable[interfaces.K]]
  override def toString = "KList(" + this.mkString(",") + ")"
  override def canEqual(that: Any) = that.isInstanceOf[KList]

  override def newBuilder: Builder[K, KList] =
    new AssocBuilder[K, KList] mapResult copy

  override def seq = contents

  override def head = contents.head
  override def tail = copy(contents.tail)
  override def isEmpty = contents.isEmpty

  def att = Attributes()
}

object KList extends CanBuildKCollection[KList] { 
  def apply(l: K*): KList = (newBuilder ++= l).result()
  
  def apply(l: Iterable[K]): KList = (newBuilder ++= l).result()

  def newBuilder: Builder[K, KList] =
    new AssocBuilder[K, KList] mapResult { l => new KList(l) }
  

  override implicit def canBuildFrom: generic.CanBuildFrom[KList, K, KList] =
    new generic.CanBuildFrom[KList, K, KList] {
      def apply(): mutable.Builder[K, KList] = newBuilder mapResult fromList
      def apply(from: KList): mutable.Builder[K, KList] = from.newBuilder
    }

  def fromJava(l: Array[K]) = apply(l: _*)

  def unapplySeq(l: KList): Option[Seq[K]] = Some(l.toSeq)
}
