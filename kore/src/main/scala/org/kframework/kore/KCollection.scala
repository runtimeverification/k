// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import org.kframework._

import collection._
import JavaConverters._
import collection.mutable.Builder

trait KCollection extends Collection[K] with K {
  type This <: KCollection

  def copy(att: Attributes): This
}

trait KAbstractCollection extends KCollection {
  type This <: KAbstractCollection

  protected[kore] def delegate: Iterable[K]

  def foreach(f: K => Unit) = delegate.foreach(f)

  def iterable = delegate

  override def hashCode() = {
    val prime = 41
    prime + delegate.hashCode
  }
}

/**
 *  Should be extended by companion objects of classes extending KCollection
 */

trait CanBuildKCollection {
  type This <: KCollection

  def apply(l: K*): This = (canBuildFrom.apply() ++= l).result
  def newBuilder(att: Attributes = Attributes()): Builder[K, This]

  protected val fromList = apply _

  implicit def canBuildFrom: generic.CanBuildFrom[This, K, This] =
    new generic.CanBuildFrom[This, K, This] {
      def apply(): mutable.Builder[K, This] = newBuilder()
      def apply(from: This): mutable.Builder[K, This] = from.newBuilder.asInstanceOf[Builder[K, This]]
    }
}
