package org.kframework.kore

import org.kframework.{kore => i}

object implementation {

  private object ConcreteClasses {

    case class Definition(att: i.Attributes, modules: Seq[i.Module]) extends i.Definition

    case class Module(name: i.ModuleName, sentences: Seq[i.Sentence], att: i.Attributes) extends i.Module

    // case class Import(name: i.ModuleName, att: i.Attributes) extends i.Import

    case class SortDeclaration(params: Seq[i.SortVariable],
                               sort: i.Sort,
                               att: i.Attributes) extends i.SortDeclaration

    case class SymbolDeclaration(symbol: i.Symbol,
                                 argSorts: Seq[i.Sort],
                                 returnSort: i.Sort,
                                 att: i.Attributes) extends i.SymbolDeclaration

    /*
    case class AliasDeclaration(alias: i.Alias,
                                argSorts: Seq[i.Sort],
                                returnSort: i.Sort,
                                att: i.Attributes) extends i.AliasDeclaration
    */

    // case class Rule(pattern: i.Pattern, att: i.Attributes) extends i.Rule

    case class AxiomDeclaration(params: Seq[i.SortVariable],
                                pattern: i.Pattern,
                                att: i.Attributes) extends i.AxiomDeclaration

    case class Attributes(patterns: Seq[i.Pattern]) extends i.Attributes

    case class Variable(name: String, sort: i.Sort) extends i.Variable

    case class Application(symbol: i.Symbol, args: Seq[i.Pattern]) extends i.Application

    // case class DomainValue(symbol: i.Symbol, value: i.Value) extends i.DomainValue

    case class Top(s: i.Sort) extends i.Top

    case class Bottom(s: i.Sort) extends i.Bottom

    case class And(s: i.Sort, _1: i.Pattern, _2: i.Pattern) extends i.And

    case class Or(s: i.Sort, _1: i.Pattern, _2: i.Pattern) extends i.Or

    case class Not(s: i.Sort, _1: i.Pattern) extends i.Not

    case class Implies(s: i.Sort, _1: i.Pattern, _2: i.Pattern) extends i.Implies

    case class Exists(s: i.Sort, v: i.Variable, p: i.Pattern) extends i.Exists

    case class ForAll(s: i.Sort, v: i.Variable, p: i.Pattern) extends i.ForAll

    // case class Next(_1: i.Pattern) extends i.Next

    // case class Rewrite(_1: i.Pattern, _2: i.Pattern) extends i.Rewrite

    case class Equals(s1: i.Sort,
                      s2: i.Sort,
                      _1: i.Pattern,
                      _2: i.Pattern) extends i.Equals

    case class StringLiteral(str: String) extends i.StringLiteral

    case class ModuleName(str: String) extends i.ModuleName

    case class SortVariable(name: String) extends i.SortVariable

    case class CompoundSort(ctr: String, params: Seq[i.Sort]) extends i.CompoundSort

    case class Symbol(ctr: String,
                      params: Seq[i.Sort]) extends i.Symbol

    /*
    case class Alias(ctr: String,
                     params: Seq[i.Sort]) extends i.Alias
    */

    // case class Value(str: String) extends i.Value

  }

  object DefaultBuilders extends i.Builders {

    import org.kframework.kore.implementation.{ConcreteClasses => d}

    def Definition(att: i.Attributes, modules: Seq[i.Module]): i.Definition = d.Definition(att, modules)

    def Module(name: i.ModuleName, sentences: Seq[i.Sentence], att: i.Attributes): i.Module = d.Module(name, sentences, att)

    // def Import(name: i.ModuleName, att: i.Attributes): i.Sentence = d.Import(name, att)

    def SortDeclaration(params: Seq[i.SortVariable], sort: i.Sort, att: i.Attributes): i.Sentence
    = d.SortDeclaration(params, sort, att)

    def SymbolDeclaration(symbol: i.Symbol,
                          argSorts: Seq[i.Sort],
                          returnSort: i.Sort,
                          att: i.Attributes): i.Sentence
    = d.SymbolDeclaration(symbol, argSorts, returnSort, att)

    /*
    def AliasDeclaration(alias: i.Alias,
                         argSorts: Seq[i.Sort],
                         returnSort: i.Sort,
                         att: i.Attributes): i.Sentence
    = d.AliasDeclaration(alias, argSorts, returnSort, att)
    */

    // def Rule(_1: i.Pattern, att: i.Attributes): i.Sentence = d.Rule(_1, att)

    def AxiomDeclaration(params: Seq[i.SortVariable],
                         _1: i.Pattern,
                         att: i.Attributes): i.Sentence
    = d.AxiomDeclaration(params, _1, att)

    def Attributes(patterns: Seq[Pattern]): i.Attributes = d.Attributes(patterns)

    // def DomainValue(symbol: i.Symbol, value: i.Value): i.Pattern = d.DomainValue(symbol, value)

    def Variable(name: String, sort: i.Sort): i.Variable = d.Variable(name, sort)

    def Application(symbol: i.Symbol, args: Seq[i.Pattern]): i.Pattern = d.Application(symbol, args)

    def Top(s: i.Sort): i.Pattern = d.Top(s)

    def Bottom(s: i.Sort): i.Pattern = d.Bottom(s)

    def And(s: i.Sort, _1: i.Pattern, _2: i.Pattern): i.Pattern = d.And(s, _1, _2)

    def Or(s: i.Sort, _1: i.Pattern, _2: i.Pattern): i.Pattern = d.Or(s, _1, _2)

    def Not(s: i.Sort, _1: i.Pattern): i.Pattern = d.Not(s, _1)

    def Implies(s: i.Sort, _1: i.Pattern, _2: i.Pattern): i.Pattern = d.Implies(s, _1, _2)

    def Exists(s: i.Sort, v: Variable, p: Pattern): i.Pattern = d.Exists(s, v, p)

    def ForAll(s: i.Sort, v: Variable, p: Pattern): i.Pattern = d.ForAll(s, v, p)

    // def Next(_1: i.Pattern): i.Pattern = d.Next(_1)

    // def Rewrite(_1: i.Pattern, _2: i.Pattern): i.Pattern = d.Rewrite(_1, _2)

    def Equals(s1: i.Sort, s2: i.Sort, _1: i.Pattern, _2: i.Pattern): i.Pattern
    = d.Equals(s1, s2, _1, _2)

    def StringLiteral(str: String): i.Pattern = d.StringLiteral(str)

    def ModuleName(str: String): i.ModuleName = d.ModuleName(str)

    def SortVariable(name: String): i.SortVariable = d.SortVariable(name)

    def CompoundSort(ctr: String, params: Seq[i.Sort]): i.CompoundSort = d.CompoundSort(ctr, params)

    def Symbol(ctr: String, params: Seq[i.Sort]): i.Symbol = d.Symbol(ctr, params)

    /*
    def Alias(ctr: String, params: Seq[i.Sort]): i.Alias = d.Alias(ctr, params)
    */

    // def Value(str: String): i.Value = d.Value(str)
  }

}

