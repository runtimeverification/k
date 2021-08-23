// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework

import java.util

import scala.jdk.CollectionConverters._
import java.util.stream.Collector
import java.util.stream.Collectors
import java.util.stream.StreamSupport
import scala.collection.mutable.Builder
import scala.collection.mutable.ListBuffer
import java.util.function.BiConsumer
import java.util.function.BinaryOperator
import java.util.function.Supplier

object Collections {
  def immutable[T](s: java.lang.Iterable[T]): Iterable[T] = s.asScala
  def immutable[T](s: java.util.Set[T]): Set[T] = s.asScala.toSet
  def immutable[T](s: java.util.List[T]): Seq[T] = s.asScala.toSeq
  def immutable[K, V](s: java.util.Map[K, V]): Map[K, V] = s.asScala.toMap
  def immutable[T](s: Array[T]): Seq[T] = s.toIndexedSeq

  def mutable[T](s: scala.List[T]): java.util.List[T] = new util.ArrayList[T](s.asJava)
  def mutable[T](s: Seq[T]): java.util.List[T] = new util.ArrayList[T](s.asJava)
  def mutable[K, V](s: Map[K, V]): java.util.Map[K, V] = new util.HashMap(s.asJava)
  def mutable[T](s: Set[T]): java.util.Set[T] = new util.HashSet[T](s.asJava)

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

  def toList[T]: Collector[T, _, Seq[T]] =
    Collectors.collectingAndThen(Collectors.toList(), (t: java.util.List[T]) => immutable(t))

  def toSet[T]: Collector[T, _, Set[T]] =
    Collectors.collectingAndThen(Collectors.toSet(), (t: java.util.Set[T]) => immutable(t))
}
