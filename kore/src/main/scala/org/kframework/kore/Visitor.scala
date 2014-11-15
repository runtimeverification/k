// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import scala.collection.immutable.Nil

trait KORETransformer[T] extends ((K) => T) with java.util.function.Function[K, T] {

  def apply(k: K): T = (k: @annotation.switch) match {
    case k: KORE => k match {
      case k: KApply => apply(k)
      case k: KRewrite => apply(k)
      case k: KToken => apply(k)
      case k: KVariable => apply(k)
    }
  }

  def apply(k: KApply): T
  def apply(k: KRewrite): T
  def apply(k: KToken): T
  def apply(k: KVariable): T
}

trait KOREVisitor extends KORETransformer[Nothing] {
  def visit(k: K) {
    apply(k)
  }
}

/* Java interfaces */

abstract class AbstractKORETransformer[T] extends KORETransformer[T]
abstract class AbstractKOREVisitor extends KOREVisitor
