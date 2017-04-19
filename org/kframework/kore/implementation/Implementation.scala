package org.kframework.kore.implementation

import org.kframework.kore.interfaces.Kore.Pattern
import org.kframework.kore.interfaces.{Builders, Kore => i}

object DefaultKore {

  case class Definition(modules: Seq[i.Module], att: i.Attributes) extends i.Definition

  case class Module(name: i.ModuleName, sentences: Seq[i.Sentence], att: i.Attributes) extends i.Module

  case class Import(name: i.ModuleName, att: i.Attributes) extends i.Import

  case class SortDeclaration(sort: i.Sort, att: i.Attributes) extends i.SortDeclaration

  case class SymbolDeclaration(sort: i.Sort, symbol: i.Symbol, args: Seq[i.Sort], att: i.Attributes) extends i.SymbolDeclaration

  case class Rule(_1: i.Pattern, att: i.Attributes) extends i.Rule

  case class Axiom(_1: i.Pattern, att: i.Attributes) extends i.Axiom

  case class Attributes(att: Seq[i.Pattern]) extends i.Attributes

  case class Variable(name: String, sort: i.Sort) extends i.Variable

  case class Application(symbol: i.Symbol, args: Seq[i.Pattern]) extends i.Application

  case class DomainValue(symbol: i.Symbol, theValue: i.Value) extends i.DomainValue

  case class Top() extends i.Top

  case class Bottom() extends i.Bottom

  case class And(_1: i.Pattern, _2: i.Pattern) extends i.And

  case class Or(_1: i.Pattern, _2: i.Pattern) extends i.Or

  case class Not(_1: i.Pattern) extends i.Not

  case class Implies(_1: i.Pattern, _2: i.Pattern) extends i.Implies

  case class Exists(v: i.Variable, _1: i.Pattern) extends i.Exists

  case class ForAll(v: i.Variable, _1: i.Pattern) extends i.ForAll

  case class Next(_1: i.Pattern) extends i.Next

  case class Rewrite(_1: i.Pattern, _2: i.Pattern) extends i.Rewrite

  case class Equals(_1: i.Pattern, _2: i.Pattern) extends i.Equals

  case class ModuleName(str: String) extends i.ModuleName

  case class Sort(str: String) extends i.Sort

  case class Name(str: String) extends i.Name

  case class Symbol(str: String) extends i.Symbol

  case class Value(str: String) extends i.Value

}

case class DefaultBuilders() extends Builders {

  import org.kframework.kore.implementation.{DefaultKore => k}
  import org.kframework.kore.interfaces.{Kore => i}


  def Definition(modules: Seq[i.Module], att: i.Attributes): i.Definition = k.Definition(modules, att)

  def Import(name: i.ModuleName, att: i.Attributes): i.Import = k.Import(name, att)

  def SortDeclaration(sort: i.Sort, att: i.Attributes): i.SortDeclaration = k.SortDeclaration(sort, att)

  def SymbolDeclaration(sort: i.Sort, symbol: i.Symbol, args: Seq[i.Sort], att: i.Attributes): i.SymbolDeclaration = k.SymbolDeclaration(sort, symbol, args, att)

  def Rule(_1: i.Pattern, att: i.Attributes): i.Rule = k.Rule(_1, att)

  def Axiom(_1: i.Pattern, att: i.Attributes): i.Axiom = k.Axiom(_1, att)

  def Module(name: i.ModuleName, sentences: Seq[i.Sentence], att: i.Attributes): i.Module = k.Module(name, sentences, att)

  def ModuleName(str: String): i.ModuleName = k.ModuleName(str)

  def Attributes(att: Seq[Pattern]): i.Attributes = k.Attributes(att)

  def Variable(name: String, sort: i.Sort): i.Variable = k.Variable(name, sort)

  def DomainValue(symbol: i.Symbol, value: i.Value): i.DomainValue = k.DomainValue(symbol, value)

  def Application(symbol: i.Symbol, args: Seq[i.Pattern]): i.Application = k.Application(symbol, args)

  def Top(): i.Top = k.Top()

  def Bottom(): i.Bottom = k.Bottom()

  def And(_1: i.Pattern, _2: i.Pattern): i.And = k.And(_1, _2)

  def Or(_1: i.Pattern, _2: i.Pattern): i.Or = k.Or(_1, _2)

  def Not(_1: i.Pattern): i.Not = k.Not(_1)

  def Implies(_1: i.Pattern, _2: i.Pattern): i.Implies = k.Implies(_1, _2)

  def Exists(v: i.Variable, _1: i.Pattern): i.Exists = k.Exists(v, _1)

  def ForAll(v: i.Variable, _1: i.Pattern): i.ForAll = k.ForAll(v, _1)

  def Next(_1: i.Pattern): i.Next = k.Next(_1)

  def Equals(_1: i.Pattern, _2: i.Pattern): i.Equals = k.Equals(_1, _2)

  def Rewrite(_1: i.Pattern, _2: i.Pattern): i.Rewrite = k.Rewrite(_1, _2)

  def Sort(str: String): i.Sort = k.Sort(str)

  def Name(str: String): i.Name = k.Name(str)

  def Symbol(str: String): i.Symbol = k.Symbol(str)

  def Value(str: String): i.Value = k.Value(str)
}

