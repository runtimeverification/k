// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import scala.collection._
import KORE._

// not sure this is the best approach -- might want a LinearSeqOptimized instead
trait GenericCollection[Elem, +This <: GenericCollection[Elem, This]] extends LinearSeq[Elem] with LinearSeqOptimized[Elem, This] {
  self: This =>
  protected val items: LinearSeq[Elem]
  override protected[this] def newBuilder: mutable.Builder[Elem, This] =
    GenericCollection.newBuilder(copy)
  def copy(s: LinearSeq[Elem]): This

  override def isEmpty: Boolean = items.isEmpty
  override def head: Elem = items.head
  override def tail: This = copy(items.tail)
}

object GenericCollection {
  def newBuilder[Elem, C <: LinearSeq[Elem]](fromList: List[Elem] => C): mutable.Builder[Elem, C] = new mutable.ListBuffer mapResult fromList
}

trait CanBuildGeneric[Elem, T <: GenericCollection[Elem, T]] {
  def apply(items: Elem*): T

  def copy(seq: Seq[Elem]): T = apply(seq: _*)

  implicit def canBuildFrom: generic.CanBuildFrom[T, Elem, T] =
    new generic.CanBuildFrom[T, Elem, T] {
      def apply(): mutable.Builder[Elem, T] = GenericCollection.newBuilder[Elem, T](copy(_: List[Elem]))
      def apply(from: T): mutable.Builder[Elem, T] = GenericCollection.newBuilder(copy(_: List[Elem]))
    }
}

trait CanBuild[T <: KCollection[T]] {
  def apply(seq: KList, att: Attributes): T

  def apply(kItems: K*): T = apply(new KList(kItems.toList), Attributes())

  def copy(seq: Seq[K], att: Attributes) = apply(new KList(seq.toList), att)

  implicit def canBuildFrom: generic.CanBuildFrom[T, K, T] =
    new generic.CanBuildFrom[T, K, T] {
      def apply(): mutable.Builder[K, T] = GenericCollection.newBuilder[K, T](copy(_: List[K], Attributes()))
      def apply(from: T): mutable.Builder[K, T] = GenericCollection.newBuilder(copy(_: List[K], from.att))
    }
}

trait Context
