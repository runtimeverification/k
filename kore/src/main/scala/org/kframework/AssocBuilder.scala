// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework

import scala.reflect.ClassTag
import scala.collection.mutable.Builder
import scala.collection.mutable.ListBuffer

trait Associative[With]

class AssocBuilder[A, R, AssocIn <: { def iterator: Iterator[A] }: ClassTag](val builder: Builder[A, R]) extends Builder[A, R] {
  def +=(elem: A): this.type = {
    val elementClass = elem.getClass()
    val collectionClass = implicitly[ClassTag[AssocIn]].runtimeClass

    if (collectionClass.isAssignableFrom(elementClass)) {
      elem.asInstanceOf[AssocIn].iterator.foreach { e => this += e }
    } else
      builder += elem

    this
  }

  def clear(): Unit = builder.clear()

  def result(): R = builder.result();
}
