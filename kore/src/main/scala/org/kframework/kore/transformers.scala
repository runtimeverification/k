// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework.kore

import scala.collection.{ IndexedSeq => _, Seq => _, _ }
import scala.jdk.CollectionConverters._

trait KTransformer[T] extends ((K) => T) with java.util.function.Function[K, T] {

  def apply(k: K): T = k match {
    case k: KApply         => apply(k: KApply)
    case k: KRewrite       => apply(k)
    case k: KToken         => apply(k)
    case k: KVariable      => apply(k)
    case k: KSequence      => apply(k: KSequence)
    case k: InjectedKLabel => apply(k)
    case k: KAs            => apply(k)
  }

  def apply(k: KApply): T

  def apply(k: KRewrite): T

  def apply(k: KToken): T

  def apply(k: KVariable): T

  def apply(k: KSequence): T

  def apply(k: InjectedKLabel): T

  def apply(k: KAs): T
}

/**
 * Folds a K term into a T. T must be a monoid with the identity defined by unit and the operation
 * by merge.
 */
abstract class FoldK[T] extends KTransformer[T] {

  def apply(k: KApply): T = merge(
    k.klabel match { case v: KVariable => apply(v); case _ => unit },
    apply(k.klist)
  )

  def apply(klist: KList): T = klist.items.asScala.map(apply).fold(unit)(merge)

  def apply(k: KRewrite): T = merge(apply(k.left), apply(k.right))

  def apply(k: KAs): T = merge(apply(k.pattern), apply(k.alias))

  def apply(k: KToken): T = unit

  def apply(k: KVariable): T = unit

  def apply(k: KSequence): T = k.items.asScala.map(apply).fold(unit)(merge)

  def apply(k: InjectedKLabel): T = k match {
    case v: KVariable => apply(v.asInstanceOf[KVariable])
    case _            => unit
  }

  def unit: T

  def merge(a: T, b: T): T
}

trait FoldKSetTransformer[E] extends FoldK[Set[E]] {}

class KVisitor extends java.util.function.Consumer[K] {

  def accept(k: K): Unit = apply(k)

  def apply(k: K): Unit =
    k match {
      case k: KApply         => apply(k: KApply)
      case k: KRewrite       => apply(k)
      case k: KToken         => apply(k)
      case k: KVariable      => apply(k)
      case k: KSequence      => apply(k: KSequence)
      case k: InjectedKLabel => apply(k)
      case k: KAs            => apply(k)
    }

  def apply(k: KApply): Unit = {
    k.klabel match {
      case k: InjectedKLabel => apply(k)
      case _                 =>
    }
    k.items.forEach(apply)
  }

  def apply(k: KRewrite): Unit = {
    apply(k.left);
    apply(k.right)
  }

  def apply(k: KAs): Unit = {
    apply(k.pattern);
    apply(k.alias)
  }

  def apply(k: KToken): Unit = {}

  def apply(k: KVariable): Unit = {}

  def apply(k: KSequence): Unit =
    k.items.forEach(apply)

  def apply(k: InjectedKLabel): Unit = k match {
    case v: KVariable => apply(v.asInstanceOf[KVariable])
    case _            =>
  }
}

/* Java interfaces */

abstract class AbstractKVisitor extends KVisitor

abstract class AbstractKTransformer[T] extends KTransformer[T]

abstract class AbstractFoldK[T] extends FoldK[T]
