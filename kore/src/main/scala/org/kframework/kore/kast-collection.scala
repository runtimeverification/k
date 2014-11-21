// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import java.util.stream.StreamSupport

import collection._
import JavaConverters._

trait Context

trait KAbstractCollection[+This <: KAbstractCollection[This]]
  extends KListBacked[This] with KCollection with K {
  self: This =>
  type ThisK <: This

  def copy(a: Attributes): ThisK = {
    copy(klist, Attributes(att.att ++ a.att))
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
  val klist: KCollection

  override def head = klist.head
  override def tail = copy(klist.tail)
  override def isEmpty = klist.isEmpty
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