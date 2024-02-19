// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.kore

import com.davekoelle.AlphanumComparator
import org.kframework.utils.errorsystem.KEMException

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
  def unapply(arg: Module): Option[(String, Seq[Declaration], Attributes)] =
    Some(arg.name, arg.decls, arg.att)
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
  def unapply(arg: SortDeclaration): Option[(Seq[SortVariable], Sort, Attributes)] =
    Some(arg.params, arg.sort, arg.att)
}

trait HookSortDeclaration extends SortDeclaration {}

object HookSortDeclaration {
  def unapply(arg: HookSortDeclaration): Option[(Seq[SortVariable], Sort, Attributes)] =
    Some(arg.params, arg.sort, arg.att)
}

trait SymbolDeclaration extends Declaration {
  def symbol: Symbol

  def argSorts: Seq[Sort]

  def returnSort: Sort

  def att: Attributes
}

object SymbolDeclaration {
  def unapply(arg: SymbolDeclaration): Option[(Symbol, Seq[Sort], Sort, Attributes)] =
    Some(arg.symbol, arg.argSorts, arg.returnSort, arg.att)
}

trait HookSymbolDeclaration extends SymbolDeclaration {}

object HookSymbolDeclaration {
  def unapply(arg: HookSymbolDeclaration): Option[(Symbol, Seq[Sort], Sort, Attributes)] =
    Some(arg.symbol, arg.argSorts, arg.returnSort, arg.att)
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
  def unapply(
      arg: AliasDeclaration
  ): Option[(Alias, Seq[Sort], Sort, Pattern, Pattern, Attributes)] =
    Some(arg.alias, arg.argSorts, arg.returnSort, arg.leftPattern, arg.rightPattern, arg.att)
}

trait AxiomDeclaration extends Declaration {
  def params: Seq[SortVariable]

  def pattern: Pattern

  def att: Attributes
}

trait ClaimDeclaration extends AxiomDeclaration {}

object AxiomDeclaration {
  def unapply(arg: AxiomDeclaration): Option[(Seq[SortVariable], Pattern, Attributes)] =
    Some(arg.params, arg.pattern, arg.att)
}

trait Attributes {
  def patterns: Seq[Pattern]
}

object Attributes {
  def unapply(arg: Attributes): Option[Seq[Pattern]] = Some(arg.patterns)
}

trait Pattern extends Comparable[Pattern] {
  def compareTo(that: Pattern): Int = Pattern.ord.compare(this, that)
}

object AlphanumOrdering extends Ordering[String] {
  def compare(a: String, b: String): Int = new AlphanumComparator().compare(a, b)
}

object Pattern {
  implicit val ord: Ordering[Pattern] = (a: Pattern, b: Pattern) =>
    (a, b) match {
      case (c: Variable, d: Variable)           => Ordering[Variable].compare(c, d)
      case (c: Application, d: Application)     => Ordering[Application].compare(c, d)
      case (c: Top, d: Top)                     => Ordering[Top].compare(c, d)
      case (c: Bottom, d: Bottom)               => Ordering[Bottom].compare(c, d)
      case (c: And, d: And)                     => Ordering[And].compare(c, d)
      case (c: Or, d: Or)                       => Ordering[Or].compare(c, d)
      case (c: Not, d: Not)                     => Ordering[Not].compare(c, d)
      case (c: Implies, d: Implies)             => Ordering[Implies].compare(c, d)
      case (c: Iff, d: Iff)                     => Ordering[Iff].compare(c, d)
      case (c: Exists, d: Exists)               => Ordering[Exists].compare(c, d)
      case (c: Forall, d: Forall)               => Ordering[Forall].compare(c, d)
      case (c: Ceil, d: Ceil)                   => Ordering[Ceil].compare(c, d)
      case (c: Floor, d: Floor)                 => Ordering[Floor].compare(c, d)
      case (c: Rewrites, d: Rewrites)           => Ordering[Rewrites].compare(c, d)
      case (c: Equals, d: Equals)               => Ordering[Equals].compare(c, d)
      case (c: Mem, d: Mem)                     => Ordering[Mem].compare(c, d)
      case (c: DomainValue, d: DomainValue)     => Ordering[DomainValue].compare(c, d)
      case (c: StringLiteral, d: StringLiteral) => Ordering[StringLiteral].compare(c, d)
      case (_: Variable, _)                     => -1
      case (_, _: Variable)                     => 1
      case (_: Application, _)                  => -1
      case (_, _: Application)                  => 1
      case (_: Top, _)                          => -1
      case (_, _: Top)                          => 1
      case (_: Bottom, _)                       => -1
      case (_, _: Bottom)                       => 1
      case (_: And, _)                          => -1
      case (_, _: And)                          => 1
      case (_: Or, _)                           => -1
      case (_, _: Or)                           => 1
      case (_: Not, _)                          => -1
      case (_, _: Not)                          => 1
      case (_: Implies, _)                      => -1
      case (_, _: Implies)                      => 1
      case (_: Iff, _)                          => -1
      case (_, _: Iff)                          => 1
      case (_: Exists, _)                       => -1
      case (_, _: Exists)                       => 1
      case (_: Forall, _)                       => -1
      case (_, _: Forall)                       => 1
      case (_: Ceil, _)                         => -1
      case (_, _: Ceil)                         => 1
      case (_: Floor, _)                        => -1
      case (_, _: Floor)                        => 1
      case (_: Rewrites, _)                     => -1
      case (_, _: Rewrites)                     => 1
      case (_: Equals, _)                       => -1
      case (_, _: Equals)                       => 1
      case (_: Mem, _)                          => -1
      case (_, _: Mem)                          => 1
      case (_: DomainValue, _)                  => -1
      case (_, _: DomainValue)                  => 1
      case (_: StringLiteral, _)                => -1
      case (_, _: StringLiteral)                => 1
      case (_, _) =>
        throw KEMException.internalError(
          "Cannot order these patterns:\n" + a.toString + "\n" + b.toString
        )
    }
}

trait Variable extends Pattern {
  def name: String

  def sort: Sort
}

object Variable {
  def unapply(arg: Variable): Option[(String, Sort)] = Some(arg.name, arg.sort)

  implicit val ord: Ordering[Variable] = Ordering.by(unapply)
}

trait SetVariable extends Variable {}

trait Application extends Pattern {
  def head: SymbolOrAlias

  def args: Seq[Pattern]
}

object Application {

  import scala.math.Ordering.Implicits._

  def unapply(arg: Application): Option[(SymbolOrAlias, Seq[Pattern])] = Some(arg.head, arg.args)

  implicit val ord: Ordering[Application] = Ordering.by(unapply)
}

trait Top extends Pattern {
  def s: Sort
}

object Top {
  def unapply(arg: Top): Option[Sort] = Some(arg.s)

  implicit val ord: Ordering[Top] = Ordering.by(unapply)
}

trait Bottom extends Pattern {
  def s: Sort
}

object Bottom {
  def unapply(arg: Bottom): Option[Sort] = Some(arg.s)

  implicit val ord: Ordering[Bottom] = Ordering.by(unapply)
}

trait And extends Pattern {
  def s: Sort

  def args: Seq[Pattern]
}

object And {

  import scala.math.Ordering.Implicits._

  def unapply(arg: And): Option[(Sort, Seq[Pattern])] = Some(arg.s, arg.args)

  implicit val ord: Ordering[And] = Ordering.by(unapply)
}

trait Or extends Pattern {
  def s: Sort

  def args: Seq[Pattern]
}

object Or {

  import scala.math.Ordering.Implicits._

  def unapply(arg: Or): Option[(Sort, Seq[Pattern])] = Some(arg.s, arg.args)

  implicit val ord: Ordering[Or] = Ordering.by(unapply)
}

trait Not extends Pattern {
  def s: Sort

  def _1: Pattern
}

object Not {
  def unapply(arg: Not): Option[(Sort, Pattern)] = Some(arg.s, arg._1)

  implicit val ord: Ordering[Not] = Ordering.by(unapply)
}

trait Implies extends Pattern {
  def s: Sort

  def _1: Pattern

  def _2: Pattern
}

object Implies {
  def unapply(arg: Implies): Option[(Sort, Pattern, Pattern)] = Some(arg.s, arg._1, arg._2)

  implicit val ord: Ordering[Implies] = Ordering.by(unapply)
}

trait Iff extends Pattern {
  def s: Sort

  def _1: Pattern

  def _2: Pattern
}

object Iff {
  def unapply(arg: Iff): Option[(Sort, Pattern, Pattern)] = Some(arg.s, arg._1, arg._2)

  implicit val ord: Ordering[Iff] = Ordering.by(unapply)
}

trait Exists extends Pattern {
  // this is the sort of the whole exists pattern, not the sort of the binding variable v
  def s: Sort

  def v: Variable

  def p: Pattern
}

object Exists {
  def unapply(arg: Exists): Option[(Sort, Variable, Pattern)] = Some(arg.s, arg.v, arg.p)

  implicit val ord: Ordering[Exists] = Ordering.by(unapply)
}

trait Forall extends Pattern {
  def s: Sort

  def v: Variable

  def p: Pattern
}

object Forall {
  def unapply(arg: Forall): Option[(Sort, Variable, Pattern)] = Some(arg.s, arg.v, arg.p)

  implicit val ord: Ordering[Forall] = Ordering.by(unapply)
}

trait Ceil extends Pattern {
  def s: Sort

  def rs: Sort

  def p: Pattern
}

object Ceil {
  def unapply(arg: Ceil): Option[(Sort, Sort, Pattern)] = Some(arg.s, arg.rs, arg.p)

  implicit val ord: Ordering[Ceil] = Ordering.by(unapply)
}

trait Floor extends Pattern {
  def s: Sort

  def rs: Sort

  def p: Pattern
}

object Floor {
  def unapply(arg: Floor): Option[(Sort, Sort, Pattern)] = Some(arg.s, arg.rs, arg.p)

  implicit val ord: Ordering[Floor] = Ordering.by(unapply)
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
 * \rewrites(P, Q) is defined as a predicate pattern floor(P implies Q) Therefore a rewrites-to
 * pattern is parametric on two sorts. One is the sort of patterns P and Q; The other is the sort of
 * the context.
 */
trait Rewrites extends Pattern with GeneralizedRewrite {
  def s: Sort // the sort of the two patterns P and Q

  def sort: Sort = s

  def _1: Pattern

  def _2: Pattern

  def getLeftHandSide: Seq[Pattern] = Seq(_1)

  def getRightHandSide: Pattern = _2
}

object Rewrites {
  def unapply(arg: Rewrites): Option[(Sort, Pattern, Pattern)] =
    Some(arg.s, arg._1, arg._2)

  implicit val ord: Ordering[Rewrites] = Ordering.by(unapply)
}

trait Equals extends Pattern with GeneralizedRewrite {
  def s: Sort // the sort of the two patterns that are being compared

  def rs: Sort // the sort of the context where the equality pattern is being placed

  def sort: Sort = rs

  def _1: Pattern

  def _2: Pattern

  def getLeftHandSide: Seq[Pattern] = _1 match {
    case Application(_, ps) => ps
  }

  def getRightHandSide: Pattern = _2
}

object Equals {
  def unapply(arg: Equals): Option[(Sort, Sort, Pattern, Pattern)] =
    Some(arg.s, arg.rs, arg._1, arg._2)

  implicit val ord: Ordering[Equals] = Ordering.by(unapply)
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

  implicit val ord: Ordering[Mem] = Ordering.by(unapply)
}

/**
 * Any domain-specific value represented as a string.
 */
trait DomainValue extends Pattern {
  def s: Sort // the sort of X and P

  def str: String // the value
}

object DomainValue {
  implicit val strOrd: Ordering[String] = AlphanumOrdering

  def unapply(arg: DomainValue): Option[(Sort, String)] = Some(arg.s, arg.str)

  implicit val ord: Ordering[DomainValue] = Ordering.by(unapply)
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

  implicit val ord: Ordering[StringLiteral] = Ordering.by(unapply)
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

/**
 * A sort can be either a sort variable or of the form C{s1,...,sn} where C is called the sort
 * constructor and s1,...,sn are sort parameters. We call sorts that are of the form C{s1,...,sn}
 * compound sorts because I don't know a better name.
 */

trait Sort

object Sort {
  implicit val ord: Ordering[Sort] = (a: Sort, b: Sort) =>
    (a, b) match {
      case (c: SortVariable, d: SortVariable) => Ordering[SortVariable].compare(c, d)
      case (c: CompoundSort, d: CompoundSort) => Ordering[CompoundSort].compare(c, d)
      case (_: SortVariable, _)               => -1
      case (_, _: SortVariable)               => 1
      case (_: CompoundSort, _)               => -1
      case (_, _: CompoundSort)               => 1
      case (_, _) =>
        throw KEMException.internalError(
          "Cannot order these sorts:\n" + a.toString + "\n" + b.toString
        )
    }
}

trait SortVariable extends Sort {
  def name: String
}

object SortVariable {
  def unapply(arg: SortVariable): Option[String] = Some(arg.name)

  implicit val ord: Ordering[SortVariable] = Ordering.by(unapply)
}

/**
 * A compound sort is of the form C{s1,...,sn} For example: Nat{} List{Nat{}} List{S} Map{S,List{S}}
 * Map{Map{Nat{},Nat{}},Nat{}}
 */
trait CompoundSort extends Sort {
  def ctr: String // sort constructor

  def params: Seq[Sort] // sort parameters
}

object CompoundSort {

  import scala.math.Ordering.Implicits._

  def unapply(arg: CompoundSort): Option[(String, Seq[Sort])] = Some(arg.ctr, arg.params)

  implicit val ord: Ordering[CompoundSort] = Ordering.by(unapply)
}

/**
 * A symbol-or-alias is of the form C{s1,...,sn} where C is called a constructor and s1,...,sn are
 * sort parameters. In the Semantics of K document, SymbolOrAlias is called the nonterminal <head>
 */
trait SymbolOrAlias {
  def ctr: String

  def params: Seq[Sort]
}

object SymbolOrAlias {

  import scala.math.Ordering.Implicits._

  def unapply(arg: SymbolOrAlias): Option[(String, Seq[Sort])] =
    Some(arg.ctr, arg.params)

  implicit val ord: Ordering[SymbolOrAlias] = Ordering.by(unapply)
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

  def SortDeclaration(params: Seq[SortVariable], sort: Sort, att: Attributes): Declaration

  def HookSortDeclaration(params: Seq[SortVariable], sort: Sort, att: Attributes): Declaration

  def SymbolDeclaration(
      symbol: Symbol,
      argSorts: Seq[Sort],
      returnSort: Sort,
      att: Attributes
  ): Declaration

  def HookSymbolDeclaration(
      symbol: Symbol,
      argSorts: Seq[Sort],
      returnSort: Sort,
      att: Attributes
  ): Declaration

  def AliasDeclaration(
      alias: Alias,
      argSorts: Seq[Sort],
      returnSort: Sort,
      leftPattern: Pattern,
      rightPattern: Pattern,
      att: Attributes
  ): Declaration

  def AxiomDeclaration(params: Seq[SortVariable], pattern: Pattern, att: Attributes): Declaration

  def ClaimDeclaration(params: Seq[SortVariable], pattern: Pattern, att: Attributes): Declaration

  def Attributes(att: Seq[Pattern]): Attributes

  def Variable(name: String, sort: Sort): Variable

  def SetVariable(name: String, sort: Sort): SetVariable

  def Application(head: SymbolOrAlias, args: Seq[Pattern]): Pattern

  def Top(s: Sort): Pattern

  def Bottom(s: Sort): Pattern

  def And(s: Sort, _1: Pattern, _2: Pattern): Pattern

  def And(s: Sort, args: Seq[Pattern]): Pattern

  def Or(s: Sort, _1: Pattern, _2: Pattern): Pattern

  def Or(s: Sort, args: Seq[Pattern]): Pattern

  def Not(s: Sort, _1: Pattern): Pattern

  def Implies(s: Sort, _1: Pattern, _2: Pattern): Pattern

  def Iff(s: Sort, _1: Pattern, _2: Pattern): Pattern

  def Exists(s: Sort, v: Variable, p: Pattern): Pattern

  def Forall(s: Sort, v: Variable, p: Pattern): Pattern

  def Ceil(s: Sort, rs: Sort, p: Pattern): Pattern

  def Floor(s: Sort, rs: Sort, p: Pattern): Pattern

  // def Next(s: Sort, _1: Pattern): Pattern

  def Rewrites(s: Sort, _1: Pattern, _2: Pattern): Pattern

  def Equals(s: Sort, rs: Sort, _1: Pattern, _2: Pattern): Pattern

  def Mem(s: Sort, rs: Sort, p: Pattern, q: Pattern): Pattern

  def DomainValue(s: Sort, str: String): Pattern

  // def Subset(s: Sort, rs:Sort, _1: Pattern, _2: Pattern): Pattern

  def StringLiteral(str: String): Pattern

  def SortVariable(name: String): SortVariable

  def CompoundSort(ctr: String, params: Seq[Sort]): CompoundSort

  def SymbolOrAlias(ctr: String, params: Seq[Sort]): SymbolOrAlias

  def Symbol(str: String, params: Seq[Sort]): Symbol

  def Alias(str: String, params: Seq[Sort]): Alias

  def LeftAssoc(ctr: (Pattern, Pattern) => Pattern, ps: Seq[Pattern]): Pattern

  def RightAssoc(ctr: (Pattern, Pattern) => Pattern, ps: Seq[Pattern]): Pattern
}
