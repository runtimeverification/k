// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework

import java.util
import java.util.function.BiConsumer
import java.util.function.BinaryOperator
import java.util.function.Supplier
import java.util.stream.StreamSupport
import scala.collection.{ IndexedSeq => _, Seq => _, _ }
import scala.collection.mutable.ListBuffer
import scala.jdk.CollectionConverters._

object Collections {
  def immutable[T](s: java.lang.Iterable[T]): Iterable[T]            = s.asScala
  def immutable[T](s: java.util.Set[T]): collection.immutable.Set[T] = s.asScala.toSet
  def immutable[T](s: java.util.List[T]): collection.immutable.Seq[T] =
    s.asScala.to(collection.immutable.Seq)
  def immutable[K, V](s: java.util.Map[K, V]): Map[K, V] = s.asScala

  def mutable[T](s: scala.List[T]): java.util.List[T]               = s.asJava
  def mutable[T](s: collection.immutable.Seq[T]): java.util.List[T] = new util.ArrayList(s.asJava)
  def mutable[K, V](s: Map[K, V]): java.util.Map[K, V]              = s.asJava

  def mutable[T](s: Set[T]): java.util.Set[T] = {
    val x = new util.HashSet[T]()
    x.addAll(s.asJava)
    x
  }

  def iterable[T](c: Iterable[T]): java.lang.Iterable[T] = c.asJava

  def optional[T](o: Option[T]): java.util.Optional[T] =
    o match {
      case None    => java.util.Optional.empty()
      case Some(s) => java.util.Optional.of(s)
    }

  def stream[T](c: Iterable[T]): java.util.stream.Stream[T] = streamIter(c.asJava)

  def streamIter[T](c: java.lang.Iterable[T]): java.util.stream.Stream[T] =
    StreamSupport.stream(c.spliterator(), false)

  def map[T](f: java.util.function.Function[T, T])(s: Set[T]): Set[T] = s.map(x => f(x))
  def map[T](f: java.util.function.Function[T, T])(
      s: collection.immutable.Set[T]
  ): collection.immutable.Set[T] =
    s.map(x => f(x))

  def map[T](f: java.util.function.Function[T, T])(s: scala.List[T]): scala.List[T] =
    s.map(x => f(x))

  def map[T](f: java.util.function.Function[T, T])(
      s: collection.immutable.Seq[T]
  ): collection.immutable.Seq[T] = s.map(x => f(x))

  def add[T](e: T)(s: collection.immutable.Set[T]): collection.immutable.Set[T]   = s ++ Set(e)
  def minus[T](e: T)(s: collection.immutable.Set[T]): collection.immutable.Set[T] = s -- Set(e)

  def or[T](
      a: collection.immutable.Set[T],
      b: collection.immutable.Set[T]
  ): collection.immutable.Set[T] = a | b

  def cons[T](e: T)(s: collection.immutable.Seq[T]): collection.immutable.Seq[T] = e +: s

  @annotation.varargs
  def List[T](es: T*): scala.List[T] = scala.List[T](es: _*)

  @annotation.varargs
  def Seq[T](es: T*): scala.collection.immutable.Seq[T] = scala.collection.immutable.Seq[T](es: _*)

  @annotation.varargs
  def Set[T](es: T*): scala.collection.immutable.Set[T] = scala.collection.immutable.Set[T](es: _*)

  def toList[T]: Collector[T, scala.List[T]] =
    Collector(() => new CombinerFromBuilder(ListBuffer()))

  def toSet[T]: Collector[T, Set[T]] =
    Collector(() => new CombinerFromBuilder(scala.collection.mutable.Set[T]()))

  def toMap[K, V]: Collector[(K, V), Map[K, V]] =
    Collector(() => new CombinerFromBuilder(scala.collection.mutable.Map[K, V]()))
}

class CombinerFromBuilder[T, R <: { def iterator: Iterator[T] }](
    protected[this] val b: mutable.Builder[T, R]
) extends Combiner[T, R] {
  type This <: CombinerFromBuilder[T, R]

  override def addOne(elem: T): this.type = {
    b.addOne(elem); this
  }

  def combine(other: Iterable[T]): Unit =
    this ++= other

  def clear(): Unit = b.clear()

  def result(): R = b.result()

  import scala.language.reflectiveCalls

  def iterator: Iterator[T] = b.result().iterator
}

trait Combiner[T, R] extends mutable.Builder[T, R] with Iterable[T] {
  type This <: Combiner[T, R]

  def combine(other: Iterable[T]): Unit

  override def knownSize: Int = super.knownSize
}

case class Collector[T, R](cf: () => Combiner[T, R])
    extends java.util.stream.Collector[T, Combiner[T, R], R] {
  def accumulator(): BiConsumer[Combiner[T, R], T] = (buffer: Combiner[T, R], e: T) => buffer += e

  def characteristics() = new java.util.HashSet()

  def combiner(): BinaryOperator[Combiner[T, R]] = (a: Combiner[T, R], b: Combiner[T, R]) => {
    a.combine(b)
    a
  }

  def finisher(): java.util.function.Function[Combiner[T, R], R] =
    (buffer: Combiner[T, R]) => buffer.result()

  def supplier(): Supplier[Combiner[T, R]] = () => cf()
}
