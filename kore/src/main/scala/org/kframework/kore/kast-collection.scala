// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import java.util.stream.StreamSupport

import collection._
import JavaConverters._

trait KAbstractCollection[+This <: KAbstractCollection[This]]
  extends KListBacked[This] with KCollection[This] with K {
  self: This =>
  type ThisK <: This

  override def foreach[B](f: K => B) {
    contents.foreach(f)
  }

  override def equals(that: Any) = that match {
    case that: This => super.equals(that)
    case _ => false
  }
}

/**
 * Describes objects which contain K's and can be iterated like a KList
 */
trait KListLike[+This <: KListLike[This]] extends LinearSeq[K] with LinearSeqOptimized[K, This] {
  self: This =>
  override def newBuilder: mutable.Builder[K, This] =
    new mutable.ListBuffer mapResult copy

  def copy(l: Iterable[K]): This

  def stream(): java.util.stream.Stream[K] = StreamSupport.stream(this.asJava.spliterator(), false)
}

/**
 * A KList-backed implementation of KList
 *
 * Implementing classes only need to provide an implementation of:
 * def copy(LinearSeq[K]): This
 *
 * @see org.kframework.kore.Attributes for an example
 *
 * KList is not based on this class because it cannot be backed by itself
 *
 */

trait KListBacked[+This <: KListLike[This]] extends KListLike[This] {
  self: This =>
  val contents: Iterable[K]

  override def head = contents.head
  override def tail = copy(contents.tail)
  override def isEmpty = contents.isEmpty
  def ks(): java.lang.Iterable[interfaces.K] = this.asJava.asInstanceOf[java.lang.Iterable[interfaces.K]]
}

/**
 * Should be extended by companion objects of classes extending KListLike
 */
trait CanBuildKListLike[This <: KListLike[This]] {
  def apply(l: K*): This

  private val fromList = apply _

  implicit def canBuildFrom: generic.CanBuildFrom[This, K, This] =
    new generic.CanBuildFrom[This, K, This] {
      def apply(): mutable.Builder[K, This] = new mutable.ListBuffer mapResult fromList
      def apply(from: This): mutable.Builder[K, This] = from.newBuilder
    }
}

trait Associative extends Iterable[K]

trait KCollection[+This <: KCollection[This]] extends K with IterableLike[K, This] {
  self: KCollection[This] =>
  type ThisK <: KCollection[This]

  def copy(ks: Iterable[K], att: Attributes): ThisK
  def copy(ks: Iterable[K]): ThisK = copy(ks, Attributes())
  def copy(att: Attributes): ThisK = copy(Seq(), att)

  def map(f: K => K): This = {
    val builder = newBuilder
    foreach {
      builder += f(_)
    }
    builder.result()
  }
}
