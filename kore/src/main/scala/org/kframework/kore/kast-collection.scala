// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import java.util.stream.StreamSupport
import collection._
import JavaConverters._
import scala.collection.mutable.Builder
import scala.reflect.ClassTag
import scala.collection.mutable.ListBuffer

trait KAbstractCollection extends KCollection with K {
  type This <: KAbstractCollection

  def delegate: Iterable[K]

  override def equals(that: Any) = {
    canEqual(that) && (that match {
      case that: KAbstractCollection => that.canEqual(KAbstractCollection.this) && delegate == that.delegate
      case _ => false
    })
  }

  def foreach(f: K => Unit) = delegate.foreach(f)

  def iterator = delegate.iterator

  def size = delegate.size

  def mkString(separator: String): String = delegate.mkString(separator)

  override def hashCode() = {
    val prime = 41
    prime + delegate.hashCode
  }
}

/**
 * Should be extended by companion objects of classes extending KListLike
 */

trait CanBuildKCollection {
  type This <: KCollection

  def apply(l: K*): This = (canBuildFrom.apply() ++= l).result
  def newBuilder: Builder[K, This]

  protected val fromList = apply _

  implicit def canBuildFrom: generic.CanBuildFrom[This, K, This] =
    new generic.CanBuildFrom[This, K, This] {
      def apply(): mutable.Builder[K, This] = newBuilder
      def apply(from: This): mutable.Builder[K, This] = from.newBuilder.asInstanceOf[Builder[K, This]]
    }
}

trait Associative[With]

trait Collection[T] {
  type This <: Collection[T]

  def newBuilder: Builder[T, This]

  def canEqual(that: Any): Boolean

  def foreach(f: T => Unit)

  def mkString(separator: String): String

  def iterator: Iterator[T]

  def isEmpty: Boolean = size == 0

  def size: Int

  def map(f: T => T): This = {
    val builder = newBuilder
    foreach { builder += f(_) }
    builder.result()
  }

  def map[R](f: T => R): List[R] = {
    val builder = ListBuffer[R]()
    foreach { builder += f(_) }
    builder.result()
  }
}

trait KCollection extends Collection[K] with K {
  type This <: KCollection

//  def copy(ks: Iterable[K], att: Attributes): This
//  def copy(ks: Iterable[K]): This = copy(ks, Attributes()).asInstanceOf[This]
  def copy(att: Attributes): This
}

class AssocBuilder[A, AssocIn <: Collection[A]: ClassTag] extends Builder[A, List[A]] {
  val buffer = new mutable.ListBuffer[A]

  def +=(elem: A): this.type = {
    if (elem.getClass().isAssignableFrom(implicitly[ClassTag[AssocIn]].runtimeClass))
      elem.asInstanceOf[AssocIn].foreach { e => buffer += e }
    else
      buffer += elem

    this
  }

  def clear(): Unit = buffer.clear()

  def result(): List[A] = buffer.result();
}
