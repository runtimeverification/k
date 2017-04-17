package org.kframework.minikore.main.implementation

import org.kframework.minikore.main.interfaces.{kore => i}

object kore {

  case class Symbol(str: String) extends i.Symbol

  case class Name(str: String) extends i.Name

  case class Value(str: String) extends i.Value

  case class Sort(str: String) extends i.Sort

  case class Top() extends i.Top

  case class Bottom() extends i.Bottom

  case class Variable(name: i.Name, sort: i.Sort) extends i.Variable

  case class DomainValue(symbol: i.Symbol, value: i.Value) extends i.DomainValue

  case class Not(p: i.Pattern) extends i.Not

  case class And(p: i.Pattern, q: i.Pattern) extends i.And

  case class Or(p: i.Pattern, q: i.Pattern) extends i.Or

  case class Implies(p: i.Pattern, q: i.Pattern) extends i.Implies

  case class Next(p: i.Pattern) extends i.Next

  case class Rewrite(p: i.Pattern, q: i.Pattern) extends i.Rewrite

  case class Equals(p: i.Pattern, q: i.Pattern) extends i.Equals

  case class Exists(v: i.Variable, q: i.Pattern) extends i.Exists

  case class ForAll(v: i.Variable, q: i.Pattern) extends i.ForAll

  case class Import(name: i.Name, att: i.Attributes = Seq.empty) extends i.Import

  case class SortDeclaration(sort: i.Sort, att: i.Attributes = Seq.empty) extends i.SortDeclaration

  case class SymbolDeclaration(sort: i.Sort, symbol: i.Symbol, args: Seq[i.Sort], att: i.Attributes = Seq.empty) extends i.SymbolDeclaration

  case class Rule(p: i.Pattern, att: i.Attributes = Seq.empty) extends i.Rule

  case class Axiom(p: i.Pattern, att: i.Attributes = Seq.empty) extends i.Axiom

  case class Module(sentences: Seq[i.Sentence], att: i.Attributes = Seq.empty) extends i.Module

  case class Definition(modules: Seq[i.Module], att: i.Attributes = Seq.empty) extends i.Definition

}

