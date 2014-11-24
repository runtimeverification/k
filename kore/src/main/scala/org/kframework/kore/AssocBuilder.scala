// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import scala.reflect.ClassTag
import scala.collection.mutable.Builder
import scala.collection.mutable.ListBuffer

trait Associative[With]

class AssocBuilder[A, AssocIn <: Collection[A]: ClassTag] extends Builder[A, List[A]] {
  val buffer = new ListBuffer[A]

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
