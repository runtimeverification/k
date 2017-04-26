package org.kframework.kore

trait Definition {
  def att: Attributes

  def modules: Seq[Module]
}

object Definition {
  def unapply(arg: Definition): Option[(Seq[Module], Attributes)] = Some(arg.modules, arg.att)
}

trait Module {
  def name: ModuleName

  def sentences: Seq[Sentence]

  def att: Attributes
}

object Module {
  def unapply(arg: Module): Option[(ModuleName, Seq[Sentence], Attributes)] = Some(arg.name, arg.sentences, arg.att)
}

trait Sentence

trait Import extends Sentence {
  def name: ModuleName

  def att: Attributes
}

object Import {
  def unapply(arg: Import): Option[(ModuleName, Attributes)] = Some(arg.name, arg.att)
}

trait SortDeclaration extends Sentence {
  def sort: Sort

  def att: Attributes
}

object SortDeclaration {
  def unapply(arg: SortDeclaration): Option[(Sort, Attributes)] = Some(arg.sort, arg.att)
}

trait SymbolDeclaration extends Sentence {
  def sort: Sort

  def symbol: Symbol

  def args: Seq[Sort]

  def att: Attributes
}

object SymbolDeclaration {
  def unapply(arg: SymbolDeclaration): Option[(Sort, Symbol, Seq[Sort], Attributes)] = Some(arg.sort, arg.symbol, arg.args, arg.att)
}


trait Rule extends Sentence {
  def pattern: Pattern

  def att: Attributes
}

object Rule {
  def unapply(arg: Rule): Option[(Pattern, Attributes)] = Some(arg.pattern, arg.att)
}

trait Axiom extends Sentence {
  def pattern: Pattern

  def att: Attributes
}

object Axiom {
  def unapply(arg: Axiom): Option[(Pattern, Attributes)] = Some(arg.pattern, arg.att)
}

trait Attributes {
  def patterns: Seq[Pattern]
}

object Attributes {
  def unapply(arg: Attributes): Option[Seq[Pattern]] = Some(arg.patterns)
}

trait Pattern

trait Variable extends Pattern

trait Application extends Pattern {
  def symbol: Symbol

  def args: Seq[Pattern]
}

object Application {
  def unapply(arg: Application): Option[(Symbol, Seq[Pattern])] = Some(arg.symbol, arg.args)
}

trait DomainValue extends Pattern {
  def symbol: Symbol

  def value: Value
}

object DomainValue {
  def unapply(arg: DomainValue): Option[(Symbol, Value)] = Some(arg.symbol, arg.value)
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

  def p: Pattern
}

object Exists {
  def unapply(arg: Exists): Option[(Variable, Pattern)] = Some(arg.v, arg.p)
}

trait ForAll extends Pattern {
  def v: Variable

  def p: Pattern
}

object ForAll {
  def unapply(arg: ForAll): Option[(Variable, Pattern)] = Some(arg.v, arg.p)
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

trait SortedVariable extends Variable {
  def name: Name

  def sort: Sort
}

object SortedVariable {
  def unapply(arg: SortedVariable): Option[(Name, Sort)] = Some(arg.name, arg.sort)
}

trait ModuleName {
  def str: String
}

object ModuleName {
  def unapply(arg: ModuleName): Option[String] = Some(arg.str)
}

trait Sort {
  def str: String
}

object Sort {
  def unapply(arg: Sort): Option[String] = Some(arg.str)
}

trait Name {
  def str: String
}

object Name {
  def unapply(arg: Name): Option[String] = Some(arg.str)
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

trait Builders {

  def Definition(att: Attributes, modules: Seq[Module]): Definition

  def Module(name: ModuleName, sentences: Seq[Sentence], att: Attributes): Module

  def Import(name: ModuleName, att: Attributes): Sentence

  def SortDeclaration(sort: Sort, att: Attributes): Sentence

  def SymbolDeclaration(sort: Sort, symbol: Symbol, args: Seq[Sort], att: Attributes): Sentence

  def Rule(pattern: Pattern, att: Attributes): Sentence

  def Axiom(pattern: Pattern, att: Attributes): Sentence

  def Attributes(att: Seq[Pattern]): Attributes

  def Application(_1: Symbol, args: Seq[Pattern]): Pattern

  def DomainValue(symbol: Symbol, value: Value): Pattern

  def Top(): Pattern

  def Bottom(): Pattern

  def And(_1: Pattern, _2: Pattern): Pattern

  def Or(_1: Pattern, _2: Pattern): Pattern

  def Not(_1: Pattern): Pattern

  def Implies(_1: Pattern, _2: Pattern): Pattern

  def Exists(v: Variable, p: Pattern): Pattern

  def ForAll(v: Variable, p: Pattern): Pattern

  def Next(_1: Pattern): Pattern

  def Equals(_1: Pattern, _2: Pattern): Pattern

  def Rewrite(_1: Pattern, _2: Pattern): Pattern

  def SortedVariable(name: Name, sort: Sort): Variable

  def ModuleName(str: String): ModuleName

  def Sort(str: String): Sort

  def Name(str: String): Name

  def Symbol(str: String): Symbol

  def Value(str: String): Value

}
