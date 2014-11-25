// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import collection.JavaConverters._
import java.util.stream.StreamSupport

object Collections {
  def immutable[T](s: java.lang.Iterable[T]): Iterable[T] = s.asScala
  def immutable[T](s: java.util.Set[T]): Set[T] = s.asScala.toSet
  def immutable[T](s: java.util.List[T]): Seq[T] = s.asScala
  def immutable[T](s: Array[T]): Seq[T] = s

  def iterable[T](c: Iterable[T]): java.lang.Iterable[T] = c.asJava
  def stream[T](c: Iterable[T]): java.util.stream.Stream[T] = StreamSupport.stream(c.asJava.spliterator(), false);
  def stream[T](c: Collection[T]): java.util.stream.Stream[T] = c.stream
  def iterable[T](c: Collection[T]): java.lang.Iterable[T] = c.iterable.asJava
}
