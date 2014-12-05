// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework

import scala.collection.mutable.Builder
import collection.JavaConverters._
import java.util.stream.StreamSupport
import scala.collection.mutable.ListBuffer

import kore._

trait Term extends Pattern with Rewriting

trait Indexed[I, T] {
  def apply(i: I): T = get(i).get
  def get(i: I): Option[T]
}

trait Collection[T] extends Term {
  type This <: Collection[T]

  def newBuilder(): Builder[T, This]

  def canEqual(that: Any): Boolean

  def foreach(f: T => Unit)

  def mkString(separator: String): String = iterable.mkString(separator)

  def iterable: Iterable[T]

  override def equals(that: Any) = {
    canEqual(that) && (that match {
      case that: Collection[_] => that.canEqual(this) && iterable == that.iterable
      case _ => false
    })
  }

  def iterator: Iterator[T] = iterable.iterator
  def list: java.util.List[T] = iterable.toList.asJava
  def stream: java.util.stream.Stream[T] = StreamSupport.stream(iterable.asJava.spliterator(), false)

  def isEmpty: Boolean = size == 0
  def size: Int = { var s = 0; foreach { x => s += 1 }; s }

  def map(f: T => T): This = {
    val builder = newBuilder()
    foreach { builder += f(_) }
    builder.result()
  }
  def map[R](f: T => R): List[R] = {
    val builder = ListBuffer[R]()
    foreach { builder += f(_) }
    builder.result()
  }
}
