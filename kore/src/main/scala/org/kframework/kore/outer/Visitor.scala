// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.outer

import org.kframework.kore.K

trait Transformer extends Function1[Definition, Definition] {
  import org.kframework.kore.outer;

  def apply(d: Definition): Definition = outer.Definition(d.requires map apply, d.modules map apply)
  def apply(r: Require): Require = r
  def apply(m: Module): Module = outer.Module(m.name, m.imports map apply, m.sentences map apply, m.att)
  def apply(s: Sentence): Sentence = s match {
    case i: Import => apply(i)
    case c: Context => apply(c)
    case r: Rule => apply(r)
    case mc: ModuleComment => apply(mc)
    case sp: SyntaxPriority => apply(sp)
    case sa: SyntaxAssociativity => apply(sa)
    case ss: SyntaxSort => apply(ss)
    case sp: SyntaxProduction => apply(sp)
  }
  def apply(c: Context): Context = outer.Context(apply(c.body), apply(c.requires), c.att)
  def apply(i: Import): Import
  def apply(r: Rule): Rule
  def apply(c: ModuleComment): ModuleComment
  def apply(s: SyntaxPriority): SyntaxPriority
  def apply(s: SyntaxAssociativity): SyntaxAssociativity
  def apply(s: SyntaxSort): SyntaxSort
  def apply(s: SyntaxProduction): SyntaxProduction
  def apply(n: NonTerminal): NonTerminal
  def apply(r: Terminal): Terminal
  def apply(r: RegexTerminal): RegexTerminal
  def apply(k: K): K
}
