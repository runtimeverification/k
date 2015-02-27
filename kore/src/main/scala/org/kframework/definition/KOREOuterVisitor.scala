// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.definition

import scala.collection.immutable.Nil

trait KOREOuterTransformer[T] extends ((OuterKORE) => T) with java.util.function.Function[OuterKORE, T] {

  def apply(e: OuterKORE): T = e match {
    case d: Definition => apply(d)
    case r: Require => apply(r)
    case m: Module => apply(m)
    case nt: NonTerminal => apply(nt)
    case t: Terminal => apply(t)
    case rt: RegexTerminal => apply(rt)
    case t: Tag => apply(t)
    case c: Context => apply(c)
    case s: SyntaxSort => apply(s)
    case s: SyntaxPriority => apply(s)
    case s: SyntaxAssociativity => apply(s)
    case r: Rule => apply(r)
    case i: Import => apply(i)
    case c: ModuleComment => apply(c)
  }

  def apply(d: Definition): T
  def apply(r: Require): T
  def apply(m: Module): T
  def apply(nt: NonTerminal): T
  def apply(t: Terminal): T
  def apply(rt: RegexTerminal): T
  def apply(t: Tag): T
  def apply(c: Context): T
  def apply(s: SyntaxSort): T
  def apply(s: SyntaxPriority): T
  def apply(s: SyntaxAssociativity): T
  def apply(r: Rule): T
  def apply(i: Import): T
  def apply(c: ModuleComment): T

}

trait KOREOuterVisitor extends KOREOuterTransformer[Nothing] {
  def visit(k: OuterKORE) {
    apply(k)
  }
}

/* Java interfaces */

abstract class AbstractKOREOuterTransformer[T] extends KOREOuterTransformer[T]
abstract class AbstractKOREOuterVisitor extends KOREOuterVisitor
