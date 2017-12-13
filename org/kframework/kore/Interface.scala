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

/*
trait Import extends Sentence {
  def name: ModuleName

  def att: Attributes
}

object Import {
  def unapply(arg: Import): Option[(ModuleName, Attributes)] = Some(arg.name, arg.att)
}
*/

trait SortDeclaration extends Sentence {
  def params: Seq[Sort]

  def sort: Sort

  def att: Attributes
}

object SortDeclaration {
  def unapply(arg: SortDeclaration): Option[(Seq[Sort], Sort, Attributes)]
  = Some(arg.params, arg.sort, arg.att)
}

trait SymbolDeclaration extends Sentence {
  def symbol: Symbol

  def argSorts: Seq[Sort]

  def returnSort: Sort

  def att: Attributes
}

object SymbolDeclaration {
  def unapply(arg: SymbolDeclaration): Option[(Symbol, Seq[Sort], Sort, Attributes)]
  = Some(arg.symbol, arg.argSorts, arg.returnSort, arg.att)
}

/*
trait Rule extends Sentence {
  def pattern: Pattern

  def att: Attributes
}

object Rule {
  def unapply(arg: Rule): Option[(Pattern, Attributes)] = Some(arg.pattern, arg.att)
}
*/

trait AxiomDeclaration extends Sentence {
  def params: Seq[Sort]

  def pattern: Pattern

  def att: Attributes
}

object AxiomDeclaration {
  def unapply(arg: AxiomDeclaration): Option[(Seq[Sort], Pattern, Attributes)]
  = Some(arg.params, arg.pattern, arg.att)
}

trait Attributes {
  def patterns: Seq[Pattern]
}

object Attributes {
  def unapply(arg: Attributes): Option[Seq[Pattern]] = Some(arg.patterns)
}

trait Pattern

trait Variable extends Pattern {
  def name: String

  def sort: Sort
}

object Variable {
  def unapply(arg: Variable): Option[(String, Sort)] = Some(arg.name, arg.sort)
}

trait Application extends Pattern {
  def symbol: Symbol

  def args: Seq[Pattern]
}

object Application {
  def unapply(arg: Application): Option[(Symbol, Seq[Pattern])] = Some(arg.symbol, arg.args)
}

/*
trait DomainValue extends Pattern {
  def symbol: Symbol

  def value: Value
}

object DomainValue {
  def unapply(arg: DomainValue): Option[(Symbol, Value)] = Some(arg.symbol, arg.value)
}
*/

trait Top extends Pattern {
  def s: Sort
}

object Top {
  def unapply(arg: Top): Option[Sort] = Some(arg.s)
}

trait Bottom extends Pattern {
  def s: Sort
}

object Bottom {
  def unapply(arg: Bottom): Option[Sort] = Some(arg.s)
}

trait And extends Pattern {
  def s: Sort

  def _1: Pattern

  def _2: Pattern
}

object And {
  def unapply(arg: And): Option[(Sort, Pattern, Pattern)] = Some(arg.s, arg._1, arg._2)
}

trait Or extends Pattern {
  def s: Sort

  def _1: Pattern

  def _2: Pattern
}

object Or {
  def unapply(arg: Or): Option[(Sort, Pattern, Pattern)] = Some(arg.s, arg._1, arg._2)
}

trait Not extends Pattern {
  def s: Sort

  def _1: Pattern
}

object Not {
  def unapply(arg: Not): Option[(Sort, Pattern)] = Some(arg.s, arg._1)
}

trait Implies extends Pattern {
  def s: Sort

  def _1: Pattern

  def _2: Pattern
}

object Implies {
  def unapply(arg: Implies): Option[(Sort, Pattern, Pattern)] = Some(arg.s, arg._1, arg._2)
}

trait Exists extends Pattern {
  def s: Sort // this is the sort of the whole exists pattern, not the sort of the binding variable v

  def v: Variable

  def p: Pattern
}

object Exists {
  def unapply(arg: Exists): Option[(Sort, Variable, Pattern)] = Some(arg.s, arg.v, arg.p)
}

trait ForAll extends Pattern {
  def s: Sort

  def v: Variable

  def p: Pattern
}

object ForAll {
  def unapply(arg: ForAll): Option[(Sort, Variable, Pattern)] = Some(arg.s, arg.v, arg.p)
}

/*
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
*/

trait Equals extends Pattern {
  def s1: Sort // the sort of the two patterns that are being compared

  def s2: Sort // the sort of the context where the equality pattern is being placed

  def _1: Pattern

  def _2: Pattern
}

object Equals {
  def unapply(arg: Equals): Option[(Sort, Sort, Pattern, Pattern)]
  = Some(arg.s1, arg.s2, arg._1, arg._2)
}

/* for now all variables are sorted variables.
trait SortedVariable extends Variable {
  def name: Name

  def sort: Sort
}

object SortedVariable {
  def unapply(arg: SortedVariable): Option[(Name, Sort)] = Some(arg.name, arg.sort)
}
*/

trait ModuleName {
  def str: String
}

object ModuleName {
  def unapply(arg: ModuleName): Option[String] = Some(arg.str)
}

// A sort can be either a sort variable or of the form C{s1,...,sn}
// where C is called the sort constructor and s1,...,sn are sort parameters.
// We call sorts that are of the form C{s1,...,sn} compound sorts because
// I don't know a better name.
trait Sort

trait SortVariable extends Sort {
  def name: String
}

object SortVariable {
  def unapply(arg: SortVariable): Option[String] = Some(arg.name)
}

// A compound sort is of the form C{s1,...,sn}
// For example:
// Nat{} List{Nat{}} List{S} Map{S,List{S}} Map{Map{Nat{},Nat{}},Nat{}}
trait CompoundSort extends Sort {
  def ctr: String        // sort constructor
  def params: Seq[Sort]  // sort parameters
}

object CompoundSort {
  def unapply(arg: CompoundSort): Option[(String, Seq[Sort])] = Some(arg.ctr, arg.params)
}

/* A symbol is of the form C{s1,...,sn} where C is called a symbol constructor and
 * s1,...,sn are sort parameters.
 * For example:
 * zero{}, nil{S}, nil{Nat{}}, plus{}, cons{S}, cons{Nat{}} are symbols
 */
trait Symbol {
  def ctr: String

  def params: Seq[Sort]
}

object Symbol {
  def unapply(arg: Symbol): Option[(String, Seq[Sort])]
  = Some(arg.ctr, (arg.params))
}

/*
trait Name {
  def str: String
}

object Name {
  def unapply(arg: Name): Option[String] = Some(arg.str)
}

*/

/*
trait Value {
  def str: String
}

object Value {
  def unapply(arg: Value): Option[String] = Some(arg.str)
}
*/

trait Builders {

  def Definition(att: Attributes, modules: Seq[Module]): Definition

  def Module(name: ModuleName, sentences: Seq[Sentence], att: Attributes): Module

  // def Import(name: ModuleName, att: Attributes): Sentence

  def SortDeclaration(params: Seq[Sort],
                      sort: Sort,
                      att: Attributes): Sentence

  def SymbolDeclaration(symbol: Symbol,
                        argSorts: Seq[Sort],
                        returnSort: Sort,
                        att: Attributes): Sentence

  // def Rule(pattern: Pattern, att: Attributes): Sentence

  def AxiomDeclaration(params: Seq[Sort],
                       pattern: Pattern,
                       att: Attributes): Sentence

  def Attributes(att: Seq[Pattern]): Attributes

  def Variable(name: String, sort: Sort): Pattern

  def Application(symbol: Symbol, args: Seq[Pattern]): Pattern

  // def DomainValue(symbol: Symbol, value: Value): Pattern

  def Top(s: Sort): Pattern

  def Bottom(s: Sort): Pattern

  def And(s: Sort, _1: Pattern, _2: Pattern): Pattern

  def Or(s: Sort, _1: Pattern, _2: Pattern): Pattern

  def Not(s: Sort, _1: Pattern): Pattern

  def Implies(s: Sort, _1: Pattern, _2: Pattern): Pattern

  def Exists(s:Sort, v: Variable, p: Pattern): Pattern

  def ForAll(s: Sort, v: Variable, p: Pattern): Pattern

  // def Next(_1: Pattern): Pattern

  def Equals(s1: Sort, s2:Sort, _1: Pattern, _2: Pattern): Pattern

  // def Rewrite(_1: Pattern, _2: Pattern): Pattern

  def ModuleName(str: String): ModuleName

  def SortVariable(name: String): SortVariable

  def CompoundSort(ctr: String, params: Seq[Sort]): CompoundSort

  // def Name(str: String): Name

  def Symbol(str: String, params: Seq[Sort]): Symbol

  // def Value(str: String): Value

}
