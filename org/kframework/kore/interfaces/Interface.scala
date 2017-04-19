package org.kframework.kore.interfaces

object Kore {

  trait Definition {
    val modules: Seq[Module]
    val att: Attributes
  }

  object Definition {
    def unapply(arg: Definition): Option[(Seq[Module], Attributes)] = Some(arg.modules, arg.att)
  }

  trait Module {
    val name: ModuleName
    val sentences: Seq[Sentence]
    val att: Attributes
  }

  object Module {
    def unapply(arg: Module): Option[(ModuleName, Seq[Sentence], Attributes)] = Some(arg.name, arg.sentences, arg.att)
  }

  trait Sentence {
    val att: Attributes
  }

  trait Import extends Sentence {
    val name: ModuleName
  }

  object Import {
    def unapply(arg: Import): Option[(ModuleName, Attributes)] = Some(arg.name, arg.att)
  }

  trait SortDeclaration extends Sentence {
    val sort: Sort
  }

  object SortDeclaration {
    def unapply(arg: SortDeclaration): Option[(Sort, Attributes)] = Some(arg.sort, arg.att)
  }

  trait SymbolDeclaration extends Sentence {
    val sort: Sort
    val symbol: Symbol
    val args: Seq[Sort]
  }

  object SymbolDeclaration {
    def unapply(arg: SymbolDeclaration): Option[(Sort, Symbol, Seq[Sort], Attributes)] = Some(arg.sort, arg.symbol, arg.args, arg.att)
  }


  trait Rule extends Sentence {
    val _1: Pattern
  }

  object Rule {
    def unapply(arg: Rule): Option[(Pattern, Attributes)] = Some(arg._1, arg.att)
  }

  trait Axiom extends Sentence {
    val _1: Pattern
  }

  object Axiom {
    def unapply(arg: Axiom): Option[(Pattern, Attributes)] = Some(arg._1, arg.att)
  }

  trait Attributes {
    def att: Seq[Pattern]
  }

  object Attributes {
    def unapply(arg: Attributes): Option[Seq[Pattern]] = Some(arg.att)
  }


  trait Pattern

  trait Variable extends Pattern {
    val name: String
    val sort: Sort
  }

  object Variable {
    def unapply(arg: Variable): Option[(String, Sort)] = Some(arg.name, arg.sort)
  }

  trait Application extends Pattern {
    val symbol: Symbol
    val args: Seq[Pattern]
  }

  object Application {
    def unapply(arg: Application): Option[(Symbol, Seq[Pattern])] = Some(arg.symbol, arg.args)
  }

  trait DomainValue extends Pattern {
    def symbol: Symbol
    def theValue: Value
  }

  object DomainValue {
    def unapply(arg: DomainValue): Option[(Symbol, Value)] = Some(arg.symbol, arg.theValue)
  }

  trait Top extends Pattern

  object Top {
    def unapply(arg: Top): Boolean = true
  }

  trait Bottom extends Pattern

  object Bottom {
    def unapply(arg: Bottom): Boolean = true
  }

  trait And extends Pattern {
    def _1: Pattern
    def _2: Pattern
  }

  object And {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }

  trait Or extends Pattern {
    def _1: Pattern
    def _2: Pattern
  }

  object Or {
    def unapply(arg: Or): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }

  trait Not extends Pattern {
    def _1: Pattern
  }

  object Not {
    def unapply(arg: Not): Option[Pattern] = Some(arg._1)
  }

  trait Implies extends Pattern {
    def _1: Pattern
    def _2: Pattern
  }

  object Implies {
    def unapply(arg: Implies): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }

  trait Exists extends Pattern {
    def v: Variable
    def _1: Pattern
  }

  object Exists {
    def unapply(arg: Exists): Option[(Variable, Pattern)] = Some(arg.v, arg._1)
  }

  trait ForAll extends Pattern {
    def v: Variable
    def _1: Pattern
  }

  object ForAll {
    def unapply(arg: ForAll): Option[(Variable, Pattern)] = Some(arg.v, arg._1)
  }

  trait Next extends Pattern {
    def _1: Pattern
  }

  object Next {
    def unapply(arg: Next): Option[Pattern] = Some(arg._1)
  }


  trait Rewrite extends Pattern {
    def _1: Pattern
    def _2: Pattern
  }

  object Rewrite {
    def unapply(arg: Rewrite): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }

  trait Equals extends Pattern {
    def _1: Pattern
    def _2: Pattern
  }

  object Equals {
    def unapply(arg: Equals): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }

  trait ModuleName {
    def str: String
  }

  object ModuleName {
    def unapply(arg: ModuleName): Option[String] = Some(arg.str)
  }

  trait Name {
    def str: String
  }

  object Name {
    def unapply(arg: Name): Option[String] = Some(arg.str)
  }

  trait Sort {
    def str: String
  }

  object Sort {
    def unapply(arg: Sort): Option[String] = Some(arg.str)
  }

  trait Symbol {
    def str: String
  }

  object Symbol {
    def unapply(arg: Symbol): Option[String] = Some(arg.str)
  }

  trait Value {
    def str: String
  }

  object Value {
    def unapply(arg: Value): Option[String] = Some(arg.str)
  }

}


trait Builders {

  import Kore._

  def Definition(modules: Seq[Module], att: Attributes): Definition

  def Module(name: ModuleName, sentences: Seq[Sentence], att: Attributes): Module

  def Import(name: ModuleName, att: Attributes): Import

  def SortDeclaration(sort: Sort, att: Attributes): SortDeclaration

  def SymbolDeclaration(sort: Sort, symbol: Symbol, args: Seq[Sort], att: Attributes): SymbolDeclaration

  def Rule(p: Pattern, att: Attributes): Rule

  def Axiom(p: Pattern, att: Attributes): Axiom

  def Attributes(att: Seq[Pattern]): Attributes

  def Variable(name: String, sort: Sort): Variable

  def Application(p: Symbol, args: Seq[Pattern]): Pattern

  def DomainValue(symbol: Symbol, value: Value): Pattern

  def Top(): Top

  def Bottom(): Bottom

  def And(p: Pattern, q: Pattern): Pattern

  def Or(p: Pattern, q: Pattern): Pattern

  def Not(p: Pattern): Pattern

  def Implies(p: Pattern, q: Pattern): Pattern

  def Exists(v: Variable, p: Pattern): Pattern

  def ForAll(v: Variable, p: Pattern): Pattern

  def Next(p: Pattern): Pattern

  def Equals(p: Pattern, q: Pattern): Pattern

  def Rewrite(p: Pattern, q: Pattern): Pattern

  def ModuleName(str: String): ModuleName

  def Sort(str: String): Sort

  def Symbol(str: String): Symbol

  def Value(str: String): Value

}

