// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import org.kframework._
import org.kframework.tiny.Reflection
import org.kframework.tiny.builtin.KAnd

import collection._
import JavaConverters._
import scala.collection.mutable.{ListBuffer, Builder}

trait KCollection extends Collection[K] with K {
  type This <: KCollection

  def transform(t: K => Option[K]): K = {
    val transformedChildren: K = this map { c => c.transform(t) }
    t.apply(transformedChildren).getOrElse(transformedChildren)
  }

  def find(f: K => Boolean): immutable.Set[K] = {
    val fromChildren = (this.iterable flatMap { _.find(f) }).toSet

    fromChildren | (if (f(this)) Set(this) else Set())
  }
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

trait WithDelegation extends KCollection {
  def newBuilder(): Builder[K, This] = ListBuffer() mapResult { l => copy(att) }
}

trait IsProduct extends Product {
  val delegate: Iterable[K] = productIterator.collect({ case k: K => k }).toIterable
}

trait SimpleCaseClass extends KAbstractCollection with WithDelegation with IsProduct {
  val companion = Reflection.findObject(this.getClass.getCanonicalName)

  //  override def copy(children: Iterator[K], att: Attributes): This = {
  //    Reflection.invokeMethod(companion, "apply", Seq(children.toSeq :+ att)).asInstanceOf[This]
  //  }
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
