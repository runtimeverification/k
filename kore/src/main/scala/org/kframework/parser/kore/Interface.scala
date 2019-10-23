package org.kframework.parser.kore

trait Definition {
  def att: Attributes

  def modules: Seq[Module]
}

object Definition {
  def unapply(arg: Definition): Option[(Seq[Module], Attributes)] = Some(arg.modules, arg.att)
}

trait Module {
  def name: String

  def decls: Seq[Declaration]

  def att: Attributes
}

object Module {
  def unapply(arg: Module): Option[(String, Seq[Declaration], Attributes)] = Some(arg.name, arg.decls, arg.att)
}

trait Declaration

trait Import extends Declaration {
  def name: String

  def att: Attributes
}

object Import {
  def unapply(arg: Import): Option[(String, Attributes)] = Some(arg.name, arg.att)
}

trait SortDeclaration extends Declaration {
  def params: Seq[SortVariable]

  def sort: Sort

  def att: Attributes
}

object SortDeclaration {
  def unapply(arg: SortDeclaration): Option[(Seq[SortVariable], Sort, Attributes)]
  = Some(arg.params, arg.sort, arg.att)
}

trait HookSortDeclaration extends SortDeclaration {
}

object HookSortDeclaration {
  def unapply(arg: HookSortDeclaration): Option[(Seq[SortVariable], Sort, Attributes)]
  = Some(arg.params, arg.sort, arg.att)
}

trait SymbolDeclaration extends Declaration {
  def symbol: Symbol

  def argSorts: Seq[Sort]

  def returnSort: Sort

  def att: Attributes
}

object SymbolDeclaration {
  def unapply(arg: SymbolDeclaration): Option[(Symbol, Seq[Sort], Sort, Attributes)]
  = Some(arg.symbol, arg.argSorts, arg.returnSort, arg.att)
}

trait HookSymbolDeclaration extends SymbolDeclaration {
}

object HookSymbolDeclaration {
  def unapply(arg: HookSymbolDeclaration): Option[(Symbol, Seq[Sort], Sort, Attributes)]
  = Some(arg.symbol, arg.argSorts, arg.returnSort, arg.att)
}

trait AliasDeclaration extends Declaration {
  def alias: Alias

  def argSorts: Seq[Sort]

  def returnSort: Sort

  def leftPattern: Pattern

  def rightPattern: Pattern

  def att: Attributes
}

object AliasDeclaration {
  def unapply(arg: AliasDeclaration): Option[(Alias, Seq[Sort], Sort, Pattern, Pattern, Attributes)]
  = Some(arg.alias, arg.argSorts, arg.returnSort, arg.leftPattern, arg.rightPattern, arg.att)
}

trait AxiomDeclaration extends Declaration {
  def params: Seq[SortVariable]

  def pattern: Pattern

  def att: Attributes
}

trait ClaimDeclaration extends  AxiomDeclaration {}

object AxiomDeclaration {
  def unapply(arg: AxiomDeclaration): Option[(Seq[SortVariable], Pattern, Attributes)]
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

trait SetVariable extends Variable {}

trait Application extends Pattern {
  def head: SymbolOrAlias

  def args: Seq[Pattern]
}

object Application {
  def unapply(arg: Application): Option[(SymbolOrAlias, Seq[Pattern])] = Some(arg.head, arg.args)
}

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

trait Iff extends Pattern {
  def s: Sort

  def _1: Pattern

  def _2: Pattern
}

object Iff {
  def unapply(arg: Iff): Option[(Sort, Pattern, Pattern)] = Some(arg.s, arg._1, arg._2)
}

trait Exists extends Pattern {
  def s: Sort // this is the sort of the whole exists pattern, not the sort of the binding variable v

  def v: Variable

  def p: Pattern
}

object Exists {
  def unapply(arg: Exists): Option[(Sort, Variable, Pattern)] = Some(arg.s, arg.v, arg.p)
}

trait Forall extends Pattern {
  def s: Sort

  def v: Variable

  def p: Pattern
}

object Forall {
  def unapply(arg: Forall): Option[(Sort, Variable, Pattern)] = Some(arg.s, arg.v, arg.p)
}

trait Ceil extends Pattern {
  def s: Sort

  def rs: Sort

  def p: Pattern
}

object Ceil {
  def unapply(arg: Ceil): Option[(Sort, Sort, Pattern)] = Some(arg.s, arg.rs, arg.p)
}

trait Floor extends Pattern {
  def s: Sort

  def rs: Sort

  def p: Pattern
}

object Floor {
  def unapply(arg: Floor): Option[(Sort, Sort, Pattern)] = Some(arg.s, arg.rs, arg.p)
}
// trait Next extends Pattern {
//   def s: Sort
//
//   def _1: Pattern
// }

// object Next {
//   def unapply(arg: Next): Option[(Sort, Pattern)] = Some(arg.s, arg._1)
// }

trait GeneralizedRewrite {
  def sort: Sort
  def getLeftHandSide: Seq[Pattern]
  def getRightHandSide: Pattern
}

/**
  * \rewrites(P, Q) is defined as a predicate pattern floor(P implies Q)
  * Therefore a rewrites-to pattern is parametric on two sorts.
  * One is the sort of patterns P and Q;
  * The other is the sort of the context.
  */
trait Rewrites extends Pattern with GeneralizedRewrite {
  def s: Sort // the sort of the two patterns P and Q

  def sort = s

  def _1: Pattern

  def _2: Pattern

  def getLeftHandSide = Seq(_1)
  def getRightHandSide = _2
}

object Rewrites {
  def unapply(arg: Rewrites): Option[(Sort, Pattern, Pattern)] =
    Some(arg.s, arg._1, arg._2)
}

trait Equals extends Pattern with GeneralizedRewrite {
  def s: Sort // the sort of the two patterns that are being compared

  def rs: Sort // the sort of the context where the equality pattern is being placed

  def sort = rs

  def _1: Pattern

  def _2: Pattern

  def getLeftHandSide = _1 match {
    case Application(_, ps) => ps
  }

  def getRightHandSide = _2
}

object Equals {
  def unapply(arg: Equals): Option[(Sort, Sort, Pattern, Pattern)] = Some(arg.s, arg.rs, arg._1, arg._2)
}

/**
  * Membership, denoted as \in(P, Q) === \ceil(P and Q)
  */
trait Mem extends Pattern {
  def s: Sort // the sort of X and P

  def rs: Sort // the context sort

  def p: Pattern // the l.h.s.

  def q: Pattern // the r.h.s.
}

object Mem {
  def unapply(arg: Mem): Option[(Sort, Sort, Pattern, Pattern)] = Some(arg.s, arg.rs, arg.p, arg.q)
}

/**
  * Any domain-specific value represented as a string.
  */
trait DomainValue extends Pattern {
  def s: Sort // the sort of X and P

  def str: String // the value
}

object DomainValue {
  def unapply(arg: DomainValue): Option[(Sort, String)] = Some(arg.s, arg.str)
}

/**
  * \subset(P,Q) is a predicate pattern that checks whether P is a subset of Q.
  */
// trait Subset extends Pattern {
//   def s: Sort // the sort of P and Q
//
//   def rs: Sort // the context sort
//
//   def _1: Pattern
//
//   def _2: Pattern
// }
//
// object Subset {
//   def unapply(arg: Subset): Option[(Sort, Sort, Pattern, Pattern)] =
//     Some(arg.s, arg.rs, arg._1, arg._2)
// }

// String literals <string> are considered as meta-level patterns of sort #String
trait StringLiteral extends Pattern {
  def str: String
}

object StringLiteral {
  def unapply(arg: StringLiteral): Option[String] = Some(arg.str)
}

// Domain Values are needed to merge Kore to K.
// The data structure for DomainValue is temporary.
// It is designed and implemented just to make sure that we can
// merge Kore to K.
// trait DomainValue extends Pattern {
//   def sortStr: String   // a string that represents the sort of the value, e.g., "Bool", "Int", etc
//
//   def valueStr: String  // a string that represents the value, e.g., "12345", "0x12345", etc
// }
//
// object DomainValue extends Pattern {
//   def unapply(arg: DomainValue): Option[(String, String)] = Some(arg.sortStr, arg.valueStr)
// }


/** A sort can be either a sort variable or of the form C{s1,...,sn}
  * where C is called the sort constructor and s1,...,sn are sort parameters.
  * We call sorts that are of the form C{s1,...,sn} compound sorts because
  * I don't know a better name.
  */

trait Sort

trait SortVariable extends Sort {
  def name: String
}

object SortVariable {
  def unapply(arg: SortVariable): Option[String] = Some(arg.name)
}

/** A compound sort is of the form C{s1,...,sn}
  * For example:
  * Nat{} List{Nat{}} List{S} Map{S,List{S}} Map{Map{Nat{},Nat{}},Nat{}}
  */
trait CompoundSort extends Sort {
  def ctr: String        // sort constructor
  def params: Seq[Sort]  // sort parameters
}

object CompoundSort {
  def unapply(arg: CompoundSort): Option[(String, Seq[Sort])] = Some(arg.ctr, arg.params)
}

/** A symbol-or-alias is of the form C{s1,...,sn}
  * where C is called a constructor and s1,...,sn are sort parameters.
  * In the Semantics of K document, SymbolOrAlias is called the nonterminal <head>
  */
trait SymbolOrAlias {
  def ctr: String

  def params: Seq[Sort]
}

object SymbolOrAlias {
  def unapply(arg: SymbolOrAlias): Option[(String, Seq[Sort])] =
    Some(arg.ctr, arg.params)
}

trait Symbol extends SymbolOrAlias

object Symbol {
  def unapply(arg: Symbol): Option[(String, Seq[Sort])] = Some(arg.ctr, arg.params)
}

trait Alias extends SymbolOrAlias

object Alias {
  def unapply(arg: Alias): Option[(String, Seq[Sort])] = Some(arg.ctr, arg.params)
}

trait Builders {

  def Definition(att: Attributes, modules: Seq[Module]): Definition

  def Module(name: String, sens: Seq[Declaration], att: Attributes): Module

  def Import(name: String, att: Attributes): Declaration

  def SortDeclaration(params: Seq[SortVariable],
                      sort: Sort,
                      att: Attributes): Declaration

  def HookSortDeclaration(params: Seq[SortVariable],
                      sort: Sort,
                      att: Attributes): Declaration

  def SymbolDeclaration(symbol: Symbol,
                        argSorts: Seq[Sort],
                        returnSort: Sort,
                        att: Attributes): Declaration

  def HookSymbolDeclaration(symbol: Symbol,
                        argSorts: Seq[Sort],
                        returnSort: Sort,
                        att: Attributes): Declaration

  def AliasDeclaration(alias: Alias,
                       argSorts: Seq[Sort],
                       returnSort: Sort,
                       leftPattern: Pattern,
                       rightPattern: Pattern,
                       att: Attributes): Declaration

  def AxiomDeclaration(params: Seq[SortVariable],
                       pattern: Pattern,
                       att: Attributes): Declaration

  def ClaimDeclaration(params: Seq[SortVariable],
                       pattern: Pattern,
                       att: Attributes): Declaration

  def Attributes(att: Seq[Pattern]): Attributes

  def Variable(name: String, sort: Sort): Variable

  def SetVariable(name: String, sort: Sort): SetVariable

  def Application(head: SymbolOrAlias, args: Seq[Pattern]): Pattern

  def Top(s: Sort): Pattern

  def Bottom(s: Sort): Pattern

  def And(s: Sort, _1: Pattern, _2: Pattern): Pattern

  def Or(s: Sort, _1: Pattern, _2: Pattern): Pattern

  def Not(s: Sort, _1: Pattern): Pattern

  def Implies(s: Sort, _1: Pattern, _2: Pattern): Pattern

  def Iff(s: Sort, _1: Pattern, _2: Pattern): Pattern

  def Exists(s:Sort, v: Variable, p: Pattern): Pattern

  def Forall(s: Sort, v: Variable, p: Pattern): Pattern

  def Ceil(s: Sort, rs: Sort, p: Pattern): Pattern

  def Floor(s: Sort, rs: Sort, p: Pattern): Pattern

  // def Next(s: Sort, _1: Pattern): Pattern

  def Rewrites(s: Sort, _1: Pattern, _2: Pattern): Pattern

  def Equals(s: Sort, rs:Sort, _1: Pattern, _2: Pattern): Pattern

  def Mem(s: Sort, rs:Sort, p: Pattern, q: Pattern): Pattern

  def DomainValue(s: Sort, str:String): Pattern

  // def Subset(s: Sort, rs:Sort, _1: Pattern, _2: Pattern): Pattern

  def StringLiteral(str: String): Pattern

  def SortVariable(name: String): SortVariable

  def CompoundSort(ctr: String, params: Seq[Sort]): CompoundSort

  def SymbolOrAlias(ctr: String, params: Seq[Sort]): SymbolOrAlias

  def Symbol(str: String, params: Seq[Sort]): Symbol

  def Alias(str: String, params: Seq[Sort]): Alias

}
