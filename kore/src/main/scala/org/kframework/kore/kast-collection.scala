// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import java.util.stream.StreamSupport
import collection._
import JavaConverters._
import scala.collection.mutable.Builder
import scala.reflect.ClassTag

trait KAbstractCollection[+This <: KAbstractCollection[This]] extends KCollection[This] with K {
  self: This =>
  type ThisK <: This

  def contents: KCollection[T forSome { type T <: KCollection[T] }]

  override def newBuilder: mutable.Builder[K, This] =
    contents.newBuilder mapResult copy

  def copy(ks: KCollection[_]): This = copy(ks, att)

  def iterator: Iterator[K] = contents.iterator

  override def equals(other: Any) = {
    other match {
      case that: KAbstractCollection[_] => that.canEqual(KAbstractCollection.this) && contents == that.contents
      case _ => false
    }
  }

  override def hashCode() = {
    val prime = 41
    prime + contents.hashCode
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
}

/**
 * Should be extended by companion objects of classes extending KListLike
 */

trait CanBuildKCollection[This <: KCollection[This]] {
  def apply(l: K*): This

  protected val fromList = apply _

  implicit def canBuildFrom: generic.CanBuildFrom[This, K, This] =
    new generic.CanBuildFrom[This, K, This] {
      def apply(): mutable.Builder[K, This] = new mutable.ListBuffer mapResult fromList
      def apply(from: This): mutable.Builder[K, This] = from.newBuilder
    }
}

trait Associative[With] extends Iterable[K]

trait KCollection[+This <: KCollection[This]] extends Iterable[K] with K with IterableLike[K, This] {
  self: KCollection[This] =>
  type ThisK <: KCollection[This]

  def copy(ks: Iterable[K], att: Attributes): ThisK
  def copy(ks: Iterable[K]): This = copy(ks, Attributes()).asInstanceOf[This]
  def copy(att: Attributes): ThisK = copy(Seq(), att)

  override def newBuilder: Builder[K, This] = ???

  def map(f: K => K): This = {
    val builder = newBuilder

    foreach {
      builder += f(_)
    }
    builder.result()
  }
}

class AssocBuilder[A, AssocIn <: Iterable[A]: ClassTag] extends Builder[A, List[A]] {
  val buffer = new mutable.ListBuffer[A]

  def +=(elem: A): this.type = {
    if (elem.getClass().isAssignableFrom(implicitly[ClassTag[AssocIn]].runtimeClass))
      buffer ++= elem.asInstanceOf[AssocIn]
    else
      buffer += elem

    this
  }

  def clear(): Unit = buffer.clear()

  def result(): List[A] = buffer.result();
}
