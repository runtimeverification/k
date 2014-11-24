// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import scala.collection.mutable.Builder
import scala.collection.mutable.ListBuffer

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