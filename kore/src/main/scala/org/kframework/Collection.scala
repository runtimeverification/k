// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework

import scala.collection.mutable.{Builder, ListBuffer}

trait Indexed[I, T] {
  def apply(i: I): T = get(i).get
  def get(i: I): Option[T]
}

trait Collection[T] {

  // Fundamental:

  type This <: Collection[T]

  def newBuilder(): Builder[T, This]

  def canEqual(that: Any): Boolean

  def iterable: Iterable[T]

  // Helpers:

  def foreach(f: T => Unit) = iterable foreach f

  def mkString(separator: String): String = iterable.mkString(separator)

  override def equals(that: Any) = {
    canEqual(that) && (that match {
      case that: Collection[_] => that.canEqual(this) && iterable == that.iterable
      case _ => false
    })
  }

  def iterator: Iterator[T] = iterable.iterator
  //  def stream: java.util.stream.Stream[T] = StreamSupport.stream(iterable.asJava.spliterator(), false)

  def isEmpty: Boolean = size == 0
  def size: Int = iterable.size

  def head: T = iterable.head

  def tail: Collection[T] = {
    val builder = newBuilder();
    iterator foreach { builder += _ }
    builder.result()
  }

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
