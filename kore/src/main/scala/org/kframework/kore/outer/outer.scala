// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.kore.outer

import org.kframework.{POSet, kore}
import org.kframework.kore.{Attributes, KLabel, KList, KToken, Sort}

trait OuterKORE

case class NonTerminalsWithUndefinedSortException(nonTerminals: Set[NonTerminal])
  extends AssertionError(nonTerminals.toString())

case class Definition(requires: Set[Require], modules: Set[Module], att: Attributes = Attributes())
  extends DefinitionToString with OuterKORE {

  def getModule(name: String): Option[Module] = modules find { case Module(`name`, _, _, _) => true; case _ => false }
}

case class Require(file: java.io.File) extends OuterKORE

case class Module(name: String, imports: Set[Module], localSentences: Set[Sentence], att: Attributes = Attributes())
  extends ModuleToString with KLabelMappings with OuterKORE {

  val sentences: Set[Sentence] = localSentences | (imports flatMap { _.sentences })

  val productions: Set[Production] = sentences collect { case p: SyntaxProduction => p }

  val definedSorts: Set[Sort] = sentences collect { case SyntaxProduction(s, _, _) => s; case SyntaxSort(s, _) => s }

  private lazy val subsortRelations: Set[(Sort, Sort)] = sentences flatMap {
    case SyntaxProduction(endSort, items, _) =>
      items collect { case NonTerminal(startSort) => (startSort, endSort) }
    case _ => Set()
  }

  private lazy val expressedPriorities: Set[(Tag, Tag)] =
    sentences
      .collect({ case SyntaxPriority(ps, _) => ps })
      .map { ps: Seq[Set[Tag]] =>
      val pairSetAndPenultimateTagSet = ps.foldLeft((Set[(Tag, Tag)](), Set[Tag]())) {
        case ((all, prev), current) =>
          val newPairs = for (a <- prev; b <- current) yield (a, b)

          (newPairs | all, current)
      }
      pairSetAndPenultimateTagSet._1 // we're only interested in the pair set part of the fold
    }.flatten
  lazy val priorities = POSet(expressedPriorities)
  lazy val leftAssoc  = buildAssoc(Associativity.Left)
  lazy val rightAssoc = buildAssoc(Associativity.Right)

  private def buildAssoc(side:Associativity.Value): Set[(Tag, Tag)] = {
    sentences
      .collect({ case SyntaxAssociativity(`side` | Associativity.NonAssoc, ps, _) => ps})
      .map { ps: Set[Tag] =>
      for (a <- ps; b <- ps) yield (a, b)
    }.flatten
  }

  lazy val subsorts = POSet(subsortRelations)

  // check that non-terminals have a defined sort
  private val nonTerminalsWithUndefinedSort = sentences flatMap {
    case SyntaxProduction(_, items, _) =>
      items collect { case nt: NonTerminal if !definedSorts.contains(nt.sort) => nt }
    case _ => Set()
  }
  if (nonTerminalsWithUndefinedSort.nonEmpty)
    throw new NonTerminalsWithUndefinedSortException(nonTerminalsWithUndefinedSort)

}

// hooked but different from core, Import is a sentence here

trait Sentence {
  // marker
  val att: Attributes
}

// deprecated
case class Context(
  body: kore.K,
  requires: kore.K,
  att: Attributes = Attributes()) extends Sentence with OuterKORE with ContextToString

case class Rule(
  body: kore.K,
  requires: kore.K,
  ensures: kore.K,
  att: Attributes) extends Sentence
with RuleToString with OuterKORE

case class ModuleComment(comment: String, att: Attributes = Attributes())
  extends Sentence with OuterKORE

case class Import(moduleName: String, att: Attributes = Attributes())
  extends Sentence with ImportToString with OuterKORE

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

trait Production {
  def sort: Sort
  def att: Attributes
  def items: Seq[ProductionItem]
  def klabel: Option[KLabel] =
    att.get(Production.kLabelAttribute).headOption map { case KList(KToken(_, s, _)) => s } map { KLabel(_) }
  def isSyntacticSubsort: Boolean =
    items.size == 1 && items.head.isInstanceOf[NonTerminal]
}

object Production {
  val kLabelAttribute = "klabel"
}

case class SyntaxSort(sort: Sort, att: Attributes = Attributes()) extends Sentence
with SyntaxSortToString with OuterKORE {
}

case class SyntaxProduction(sort: Sort, items: Seq[ProductionItem], att: Attributes = Attributes())
  extends Sentence with SyntaxProductionToString with Production

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
  def apply(sort: String): NonTerminal = NonTerminal(Sort(sort))
}
