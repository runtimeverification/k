// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.koreimplementation

import org.kframework._
import org.kframework.tiny.{Theory, Proposition, Reflection}
import org.kframework.tiny.builtin.KAnd

import collection._
import JavaConverters._
import scala.collection.mutable.{ListBuffer, Builder}
import org.kframework.tiny.Or

import UglyHack._

trait KCollection extends Collection[K] with Node {
  type This <: KCollection

  def transform(t: K => Option[K]): K = {
    val transformedChildren: K = this map { _.transform(t) }
    t.apply(transformedChildren).getOrElse(transformedChildren)
  }

  def find(f: K => Boolean): immutable.Set[K] = {
    val fromChildren = (this.iterable flatMap { _.find(f) }).toSet

    fromChildren | (if (f(this)) Set(this) else Set())
  }
}

trait KProduct extends Product with Node {
  type This <: K

  val companion = Reflection.findObject(this.getClass.getCanonicalName)

  val children: Iterator[K] = productIterator collect { case x: K => x }

  override def copy(att: Attributes): This = {
    val children = productIterator map { case x: K => x; case att: Attributes => att }

    Reflection.invokeMethod(companion, "apply", Seq(children.toSeq)).asInstanceOf[This]
  }

  override def matchAll(k: K, sideConditions: Proposition)(implicit theory: Theory): Or = ???

  override def transform(t: (K) => Option[K]): K = {
    val newChildren = productIterator map { case k: K => t(k).getOrElse(k); case att => att }

    t(Reflection.invokeMethod(companion, "apply", Seq(newChildren.toSeq)).asInstanceOf[This]).getOrElse(this)
  }

  override def find(f: (K) => Boolean): immutable.Set[K] = {
    val matchingChildren = (children flatMap { _.find(f) }).toSet
    if (f(this))
      matchingChildren + this
    else
      matchingChildren
  }
}

trait KAbstractCollection extends KCollection {
  type This <: KAbstractCollection

  protected[koreimplementation] def delegate: Iterable[K]

  def foreach(f: K => Unit) = delegate.foreach(f)

  def iterable = delegate

  override def hashCode() = {
    val prime = 41
    prime + delegate.hashCode
  }
}

trait IsProduct extends Product {
  val delegate: Iterable[K] = productIterator.collect({ case k: K => k }).toIterable
}

/**
 * Should be extended by companion objects of classes extending KCollection
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
