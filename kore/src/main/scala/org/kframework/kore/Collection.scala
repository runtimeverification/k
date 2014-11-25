// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import collection.mutable.Builder
import collection.mutable.ListBuffer
import collection.JavaConverters._
import java.util.stream.StreamSupport

trait Collection[T] {
  type This <: Collection[T]

  def newBuilder: Builder[T, This]

  def canEqual(that: Any): Boolean

  def foreach(f: T => Unit)

  def mkString(separator: String): String = iterable.mkString(separator)

  def iterable: Iterable[T]

  def list: java.util.List[T] = iterable.toList.asJava
  def stream: java.util.stream.Stream[T] = StreamSupport.stream(iterable.asJava.spliterator(), false)

  def isEmpty: Boolean = size == 0

  def size: Int = { var s = 0; foreach { x => s += 1 }; s }

  def map(f: T => T): This = {
    val builder = newBuilder
    foreach { builder += f(_) }
    builder.result()
  }

  def map[R](f: T => R): scala.List[R] = {
    val builder = ListBuffer[R]()
    foreach { builder += f(_) }
    builder.result()
  }
}
