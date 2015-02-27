// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

trait KORETransformer[T] extends ((K) => T) with java.util.function.Function[K, T] {

  def apply(k: K): T = k match {
    case k: KApply => apply(k: KApply)
    case k: KRewrite => apply(k)
    case k: KToken => apply(k)
    case k: KVariable => apply(k)
    case k: KSequence => apply(k: KSequence)
  }

  def apply(k: KApply): T
  def apply(k: KRewrite): T
  def apply(k: KToken): T
  def apply(k: KVariable): T
  def apply(k: KSequence): T
}

trait KOREVisitor extends KORETransformer[Nothing] {
  def visit(k: K) {
    apply(k)
  }
}

/* Java interfaces */

abstract class AbstractKORETransformer[T] extends KORETransformer[T]
abstract class AbstractKOREVisitor extends KOREVisitor
