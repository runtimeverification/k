package org.kframework.kore

object default {

  import org.kframework.{kore => i}

  case class Definition(modules: Seq[i.Module], att: i.Attributes) extends i.Definition

  case class Module(name: i.ModuleName, sentences: Seq[i.Sentence], att: i.Attributes) extends i.Module

  case class Import(name: i.ModuleName, att: i.Attributes) extends i.Import

  case class SortDeclaration(sort: i.Sort, att: i.Attributes) extends i.SortDeclaration

  case class SymbolDeclaration(sort: i.Sort, symbol: i.Symbol, args: Seq[i.Sort], att: i.Attributes) extends i.SymbolDeclaration

  case class Rule(_1: i.Pattern, att: i.Attributes) extends i.Rule

  case class Axiom(_1: i.Pattern, att: i.Attributes) extends i.Axiom

  case class Attributes(att: Seq[i.Pattern]) extends i.Attributes

  case class Variable(name: i.Name, sort: i.Sort) extends i.Variable

  case class Application(symbol: i.Symbol, args: Seq[i.Pattern]) extends i.Application

  case class DomainValue(symbol: i.Symbol, value: i.Value) extends i.DomainValue

  case class Top() extends i.Top

  case class Bottom() extends i.Bottom

  case class And(_1: i.Pattern, _2: i.Pattern) extends i.And

  case class Or(_1: i.Pattern, _2: i.Pattern) extends i.Or

  case class Not(_1: i.Pattern) extends i.Not

  case class Implies(_1: i.Pattern, _2: i.Pattern) extends i.Implies

  case class Exists(v: i.Variable, p: i.Pattern) extends i.Exists

  case class ForAll(v: i.Variable, p: i.Pattern) extends i.ForAll

  case class Next(_1: i.Pattern) extends i.Next

  case class Rewrite(_1: i.Pattern, _2: i.Pattern) extends i.Rewrite

  case class Equals(_1: i.Pattern, _2: i.Pattern) extends i.Equals

  case class ModuleName(str: String) extends i.ModuleName

  case class Sort(str: String) extends i.Sort

  case class Name(str: String) extends i.Name

  case class Symbol(str: String) extends i.Symbol

  case class Value(str: String) extends i.Value


  object DefaultBuilders extends i.Builders {

    import org.kframework.kore.{default => d}

    def Definition(modules: Seq[i.Module], att: i.Attributes): i.Definition = d.Definition(modules, att)

    def Import(name: i.ModuleName, att: i.Attributes): i.Import = d.Import(name, att)

    def SortDeclaration(sort: i.Sort, att: i.Attributes): i.SortDeclaration = d.SortDeclaration(sort, att)

    def SymbolDeclaration(sort: i.Sort, symbol: i.Symbol, args: Seq[i.Sort], att: i.Attributes): i.SymbolDeclaration = d.SymbolDeclaration(sort, symbol, args, att)

    def Rule(_1: i.Pattern, att: i.Attributes): i.Rule = d.Rule(_1, att)

    def Axiom(_1: i.Pattern, att: i.Attributes): i.Axiom = d.Axiom(_1, att)

    def Module(name: i.ModuleName, sentences: Seq[i.Sentence], att: i.Attributes): i.Module = d.Module(name, sentences, att)

    def ModuleName(str: String): i.ModuleName = d.ModuleName(str)

    def Attributes(att: Seq[Pattern]): i.Attributes = d.Attributes(att)

    def Variable(name: i.Name, sort: i.Sort): i.Variable = d.Variable(name, sort)

    def DomainValue(symbol: i.Symbol, value: i.Value): i.DomainValue = d.DomainValue(symbol, value)

    def Application(symbol: i.Symbol, args: Seq[i.Pattern]): i.Application = d.Application(symbol, args)

    def Top(): i.Top = d.Top()

    def Bottom(): i.Bottom = d.Bottom()

    def And(_1: i.Pattern, _2: i.Pattern): i.And = d.And(_1, _2)

    def Or(_1: i.Pattern, _2: i.Pattern): i.Or = d.Or(_1, _2)

    def Not(_1: i.Pattern): i.Not = d.Not(_1)

    def Implies(_1: i.Pattern, _2: i.Pattern): i.Implies = d.Implies(_1, _2)

    def Exists(v: i.Variable, p: i.Pattern): i.Exists = d.Exists(v, p)

    def ForAll(v: i.Variable, p: i.Pattern): i.ForAll = d.ForAll(v, p)

    def Next(_1: i.Pattern): i.Next = d.Next(_1)

    def Equals(_1: i.Pattern, _2: i.Pattern): i.Equals = d.Equals(_1, _2)

    def Rewrite(_1: i.Pattern, _2: i.Pattern): i.Rewrite = d.Rewrite(_1, _2)

    def Sort(str: String): i.Sort = d.Sort(str)

    def Name(str: String): i.Name = d.Name(str)

    def Symbol(str: String): i.Symbol = d.Symbol(str)

    def Value(str: String): i.Value = d.Value(str)
  }

}

