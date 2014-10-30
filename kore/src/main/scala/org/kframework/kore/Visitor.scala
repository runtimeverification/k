// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import scala.collection.immutable.Nil

trait KORETransformer[T] {
  def transform(k: K): T = (k: @annotation.switch) match {
    case k: KORE => k match {
      case k: KApply => transform(k)
      case k: KRewrite => transform(k)
      case k: KToken => transform(k)
      case k: KVariable => transform(k)
    }
  }

  def transform(k: KApply): T
  def transform(k: KRewrite): T
  def transform(k: KToken): T
  def transform(k: KVariable): T
}

trait KOREVisitor extends KORETransformer[Nothing] {
  def visit(k: K) {
    transform(null: K)
  }
}

/* Java interfaces */

abstract class AbstractKORETransformer[T] extends KORETransformer[T]
abstract class AbstractKOREVisitor extends KOREVisitor
