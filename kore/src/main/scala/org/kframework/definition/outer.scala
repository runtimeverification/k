// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.definition

import org.kframework.POSet
import org.kframework.attributes.Att
import org.kframework.kore._

trait OuterKORE

case class NonTerminalsWithUndefinedSortException(nonTerminals: Set[NonTerminal])
  extends AssertionError(nonTerminals.toString())

case class DivergingAttributesForTheSameKLabel(ps: Set[Production])
  extends AssertionError(ps.toString)

//object NonTerminalsWithUndefinedSortException {
//  def apply(nonTerminals: Set[NonTerminal]) =
//    new NonTerminalsWithUndefinedSortException(nonTerminals.toString, nonTerminals)
//
//}

case class Definition(
  mainModule: Module,
  mainSyntaxModule: Module,
  entryModules: Set[Module],
  att: Att = Att())
  extends DefinitionToString with OuterKORE {

  private def allModules(m: Module): Set[Module] = m.imports | (m.imports flatMap allModules) + m

  val modules = entryModules flatMap allModules

  assert(modules.contains(mainModule))
  assert(modules.contains(mainSyntaxModule))

  def getModule(name: String): Option[Module] = modules find { case Module(`name`, _, _, _) => true; case _ => false }
}

case class Module(name: String, imports: Set[Module], localSentences: Set[Sentence], att: Att = Att())
  extends ModuleToString with KLabelMappings with OuterKORE {

  val sentences: Set[Sentence] = localSentences | (imports flatMap {_.sentences})

  /** All the imported modules, calculated recursively. */
  val importedModules: Set[Module] = imports | (imports flatMap { _.importedModules })

  val productions: Set[Production] = sentences collect { case p: Production => p }

  val productionsFor: Map[KLabel, Set[Production]] =
    productions
      .collect({ case p if p.klabel != None => p })
      .groupBy(_.klabel.get)
      .map { case (l, ps) => (l, ps) }

  val sortFor: Map[KLabel, Sort] = productionsFor mapValues {_.head.sort}

  def isSort(klabel: KLabel, s: Sort) = subsorts.<(sortFor(klabel), s)

  val rules: Set[Rule] = sentences collect { case r: Rule => r }

  // Check that productions with the same #klabel have identical attributes
  //  productionsFor.foreach {
  //    case (l, ps) =>
  //      if (ps.groupBy(_.att).size != 1)
  //        throw DivergingAttributesForTheSameKLabel(ps)
  //  }

  val attributesFor: Map[KLabel, Att] = productionsFor mapValues {_.head.att}

  val signatureFor: Map[KLabel, Set[(Seq[Sort], Sort)]] =
    productionsFor mapValues {
      ps: Set[Production] =>
        ps.map {
          p: Production =>
            val params: Seq[Sort] = p.items collect { case NonTerminal(sort) => sort }
            (params, p.sort)
        }
    }

  val sortDeclarations: Set[SyntaxSort] = sentences.collect({ case s: SyntaxSort => s })

  val definedSorts: Set[Sort] = (productions map {_.sort}) ++ (sortDeclarations map {_.sort})

  val listSorts: Set[Sort] = sentences.collect({ case Production(srt, _, att1) if att1.contains("userList") => srt })

  private val subsortRelations: Set[(Sort, Sort)] = sentences collect {
    case Production(endSort, Seq(NonTerminal(startSort)), _) => (startSort, endSort)
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
  lazy val leftAssoc = buildAssoc(Associativity.Left)
  lazy val rightAssoc = buildAssoc(Associativity.Right)

  private def buildAssoc(side: Associativity.Value): Set[(Tag, Tag)] = {
    sentences
      .collect({ case SyntaxAssociativity(`side` | Associativity.NonAssoc, ps, _) => ps })
      .map { ps: Set[Tag] =>
      for (a <- ps; b <- ps) yield (a, b)
    }.flatten
  }

  val subsorts: POSet[Sort] = POSet(subsortRelations)

  // check that non-terminals have a defined sort
  private val nonTerminalsWithUndefinedSort = sentences flatMap {
    case p@Production(_, items, _) =>
      val res = items collect { case nt: NonTerminal if !definedSorts.contains(nt.sort) => nt }
      if (!res.isEmpty)
        throw new AssertionError("Could not find sort: " + res + " in production " + p + " in module " + this.name)
      res
    case _ => Set()
  }
  if (!nonTerminalsWithUndefinedSort.isEmpty)
    throw new NonTerminalsWithUndefinedSortException(nonTerminalsWithUndefinedSort)

}

// hooked but different from core, Import is a sentence here

trait Sentence {
  // marker
  val att: Att
}

// deprecated
case class Context(body: K, requires: K, att: Att = Att()) extends Sentence with OuterKORE with ContextToString

case class Rule(body: K, requires: K, ensures: K, att: Att = Att()) extends Sentence with RuleToString with OuterKORE

case class ModuleComment(comment: String, att: Att = Att()) extends Sentence with OuterKORE

// hooked

// syntax declarations

case class SyntaxPriority(priorities: Seq[Set[Tag]], att: Att = Att())
  extends Sentence with SyntaxPriorityToString with OuterKORE

object Associativity extends Enumeration {
  type Value1 = Value
  val Left, Right, NonAssoc, Unspecified = Value
}

case class SyntaxAssociativity(
  assoc: Associativity.Value,
  tags: collection.immutable.Set[Tag],
  att: Att = Att())
  extends Sentence with SyntaxAssociativityToString with OuterKORE

case class Tag(name: String) extends TagToString with OuterKORE

//trait Production {
//  def sort: Sort
//  def att: Att
//  def items: Seq[ProductionItem]
//  def klabel: Option[KLabel] =
//    att.get(Production.kLabelAttribute).headOption map { case KList(KToken(_, s, _)) => s } map { KLabel(_) }
//}

case class SyntaxSort(sort: Sort, att: Att = Att()) extends Sentence
with SyntaxSortToString with OuterKORE {
  def items = Seq()
}

case class Production(sort: Sort, items: Seq[ProductionItem], att: Att)
  extends Sentence with ProductionToString {
  lazy val klabel: Option[KLabel] = att.get[String]("#klabel") map { org.kframework.kore.KORE.KLabel(_) }

  override def equals(that: Any) = that match {
    case p@Production(`sort`, `items`, _) => this.klabel == p.klabel
    case _ => false
  }

  override def hashCode = sort.hashCode

  def isSyntacticSubsort: Boolean =
    items.size == 1 && items.head.isInstanceOf[NonTerminal]
}

object Production {
  def apply(klabel: String, sort: Sort, items: Seq[ProductionItem], att: Att = Att()): Production = {
    Production(sort, items, att + ("#klabel" -> klabel))
  }
  val kLabelAttribute = "klabel"
}

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
