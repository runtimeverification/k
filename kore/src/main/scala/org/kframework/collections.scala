// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework

import java.util

import collection.JavaConverters._
import java.util.stream.StreamSupport
import scala.collection.mutable.Builder
import scala.collection.mutable.ListBuffer
import java.util.function.BiConsumer
import java.util.function.BinaryOperator
import java.util.function.Supplier
import scala.collection.mutable.SetBuilder
import scala.collection.mutable.MapBuilder
import collection._

object Collections {
  def immutable[T](s: java.lang.Iterable[T]): Iterable[T] = s.asScala
  def immutable[T](s: java.util.Set[T]): Set[T] = s.asScala.toSet
  def immutable[T](s: java.util.List[T]): Seq[T] = s.asScala
  def immutable[K, V](s: java.util.Map[K, V]): Map[K, V] = s.asScala
  def immutable[T](s: Array[T]): Seq[T] = s

  def mutable[T](s: scala.List[T]): java.util.List[T] = s.asJava
  def mutable[T](s: Seq[T]): java.util.List[T] = s.asJava
  def mutable[K, V](s: Map[K, V]): java.util.Map[K, V] = s.asJava
  def mutable[T](s: Set[T]): java.util.Set[T] = {
    val x = new util.HashSet[T]()
    x.addAll(s.asJava)
    x
  }

  def iterable[T](c: Iterable[T]): java.lang.Iterable[T] = c.asJava
  def stream[T](c: Iterable[T]): java.util.stream.Stream[T] = StreamSupport.stream(c.asJava.spliterator(), false);

  def map[T](f: java.util.function.Function[T, T])(s: Set[T]): Set[T] = s.map(x => f(x))
  def map[T](f: java.util.function.Function[T, T])(s: scala.List[T]): scala.List[T] = s.map(x => f(x))
  def map[T](f: java.util.function.Function[T, T])(s: Seq[T]): Seq[T] = s.map(x => f(x))

  def add[T](e: T)(s: Set[T]): Set[T] = s + e
  def minus[T](e: T)(s: Set[T]): Set[T] = s - e
  def or[T](a: Set[T], b: Set[T]): Set[T] = a | b

  def cons[T](e: T)(s: Seq[T]): Seq[T] = e +: s

  @annotation.varargs def List[T](es: T*): scala.List[T] = scala.List[T](es: _*)
  @annotation.varargs def Seq[T](es: T*) = scala.collection.immutable.Seq[T](es: _*)
  @annotation.varargs def Set[T](es: T*) = scala.collection.immutable.Set[T](es: _*)

  def toList[T]: Collector[T, scala.List[T]] =
    Collector(() => new CombinerFromBuilder(ListBuffer()))

  def toSet[T]: Collector[T, Set[T]] =
    Collector(() => new CombinerFromBuilder(new SetBuilder(Set())))

  def toMap[K, V]: Collector[(K, V), Map[K, V]] =
    Collector(() => new CombinerFromBuilder(new MapBuilder(Map())))
}

class CombinerFromBuilder[T, R <: {def iterator : Iterator[T]}](protected[this] val b: Builder[T, R]) extends
Combiner[T, R] {
  type This <: CombinerFromBuilder[T, R]

  def +=(elem: T): this.type = { b += elem; this }

  def combine(other: Iterable[T]) { this ++= other }

  def clear(): Unit = b.clear()

  def result(): R = b.result()

  import scala.language.reflectiveCalls

  def iterator() = b.result().iterator
}

trait Combiner[T, R] extends Builder[T, R] with Iterable[T] {
  type This <: Combiner[T, R]

  def combine(other: Iterable[T])
}

case class Collector[T, R](cf: () => Combiner[T, R]) extends java.util.stream.Collector[T, Combiner[T, R], R] {
  def accumulator() = new BiConsumer[Combiner[T, R], T] {
    def accept(buffer: Combiner[T, R], e: T) = buffer += e
  }

  def characteristics() = new java.util.HashSet()

  def combiner() = new BinaryOperator[Combiner[T, R]] {
    def apply(a: Combiner[T, R], b: Combiner[T, R]) = {
      a.combine(b);
      a
    }
  }

  def finisher(): java.util.function.Function[Combiner[T, R], R] = new java.util.function.Function[Combiner[T, R], R] {
    def apply(buffer: Combiner[T, R]): R = buffer.result()
  }

  def supplier(): Supplier[Combiner[T, R]] = new Supplier[Combiner[T, R]] {
    def get() = cf()
  }
}
