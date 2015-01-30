// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.definition

import org.kframework.POSet
import org.kframework.kore._
import org.kframework.attributes._

trait OuterKORE

case class NonTerminalsWithUndefinedSortException(nonTerminals: Set[NonTerminal])
  extends AssertionError(nonTerminals.toString)

case class DivergingAttributesForTheSameKLabel(ps: Set[Production])
  extends AssertionError(ps.toString)

//object NonTerminalsWithUndefinedSortException {
//  def apply(nonTerminals: Set[NonTerminal]) =
//    new NonTerminalsWithUndefinedSortException(nonTerminals.toString, nonTerminals)
//
//}


case class Definition(requires: Set[Require], modules: Set[Module], att: Attributes = Attributes())
  extends DefinitionToString with OuterKORE {

  def getModule(name: String): Option[Module] = modules find { case Module(`name`, _, _, _) => true; case _ => false }
}

case class Require(file: java.io.File) extends OuterKORE

case class Module(name: String, imports: Set[Module], localSentences: Set[Sentence], att: Attributes = Attributes())
  extends ModuleToString with KLabelMappings with OuterKORE {

  val sentences: Set[Sentence] = localSentences | (imports flatMap { _.sentences })

  val productions: Set[Production] = sentences collect { case p: Production => p }

  val productionsFor: Map[KLabel, Set[Production]] = productions.groupBy(_.klabel) map {
    case (l, ps) => (l, ps)
  }

  // Check that productions with the same #klabel have identical attributes
  productionsFor.foreach {
    case (l, ps) => if (ps.groupBy(_.att).size != 1) throw DivergingAttributesForTheSameKLabel(ps)
  }

  val attributesFor: Map[KLabel, Attributes] = productionsFor mapValues { _.head.att }

  val signatureFor: Map[KLabel, Set[(Seq[Sort], Sort)]] =
    productionsFor mapValues {
      ps: Set[Production] =>
        ps.map {
          p: Production =>
            val params: Seq[Sort] = p.items collect { case NonTerminal(sort) => sort }
            (params, p.sort)
        }
    }

  val definedSorts: Set[Sort] = productions map { _.sort }

  private lazy val subsortRelations = sentences flatMap {
    case Production(_, endSort, items, _) =>
      items collect { case NonTerminal(startSort) => (startSort, endSort) }
    case _ => Set()
  }

  lazy val subsorts = POSet(subsortRelations)

  // check that non-terminals have a defined sort
  private val nonTerminalsWithUndefinedSort = sentences flatMap {
    case Production(_, _, items, _) =>
      items collect { case nt: NonTerminal if !definedSorts.contains(nt.sort) => nt }
    case _ => Set()
  }
  if (!nonTerminalsWithUndefinedSort.isEmpty)
    throw new NonTerminalsWithUndefinedSortException(nonTerminalsWithUndefinedSort)

}

// hooked but different from core, Import is a sentence here

trait Sentence {
  // marker
  val att: Attributes
}

// deprecated
case class Context(body: K, requires: K, att: Attributes = Attributes()) extends Sentence with OuterKORE with ContextToString

case class Rule(body: K, requires: K, ensures: K, att: Attributes) extends Sentence with RuleToString with OuterKORE

case class ModuleComment(comment: String, att: Attributes = Attributes()) extends Sentence with OuterKORE

case class Import(moduleName: String, att: Attributes = Attributes()) extends Sentence with ImportToString with OuterKORE

// hooked

// syntax declarations

case class SyntaxPriority(priorities: Seq[Set[Tag]], att: Attributes = Attributes())
  extends Sentence with SyntaxPriorityToString with OuterKORE

object Associativity extends Enumeration {
  type Value1 = Value
  val Left, Right, NonAssoc, Unspecified = Value
}

case class SyntaxAssociativity(
  assoc: Associativity.Value,
  tags: collection.immutable.Set[Tag],
  att: Attributes = Attributes())
  extends Sentence with SyntaxAssociativityToString with OuterKORE

case class Tag(name: String) extends TagToString with OuterKORE

//trait Production {
//  def sort: Sort
//  def att: Attributes
//  def items: Seq[ProductionItem]
//  def klabel: Option[KLabel] =
//    att.get(Production.kLabelAttribute).headOption map { case KList(KToken(_, s, _)) => s } map { KLabel(_) }
//}

object Production {
  val kLabelAttribute = "klabel"
}

case class SyntaxSort(sort: Sort, att: Attributes = Attributes()) extends Sentence
with SyntaxSortToString with OuterKORE {
  def items = Seq()
}

case class Production(klabel: KLabel, sort: Sort, items: Seq[ProductionItem], att: Attributes = Attributes())
  extends Sentence with ProductionToString

// hooked but problematic, see kast-core.k

sealed trait ProductionItem extends OuterKORE

// marker

case class NonTerminal(sort: Sort) extends ProductionItem
with NonTerminalToString

case class RegexTerminal(regex: String) extends ProductionItem with RegexTerminalToString

case class Terminal(value: String) extends ProductionItem // hooked
with TerminalToString

/* Helper constructors */
object NonTerminal {
  def apply(sort: String): NonTerminal = NonTerminal(ADT.Sort(sort))
}
