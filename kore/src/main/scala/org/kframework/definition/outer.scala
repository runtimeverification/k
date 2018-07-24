// Copyright (c) 2014-2018 K Team. All Rights Reserved.

package org.kframework.definition

import java.util.Optional
import javax.annotation.Nonnull

import dk.brics.automaton.{BasicAutomata, RegExp, RunAutomaton, SpecialOperations}
import org.kframework.POSet
import org.kframework.attributes.{Att, HasLocation, Location, Source}
import org.kframework.definition.Constructors._
import org.kframework.kore.Unapply.{KApply, KLabel}
import org.kframework.kore
import org.kframework.kore.KORE.Sort
import org.kframework.kore._
import org.kframework.utils.errorsystem.KEMException
import org.kframework.builtin.Sorts

import scala.annotation.meta.param
import scala.collection.JavaConverters._
import collection._
import scala.collection.Set

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
                       entryModules: Set[Module],
                       att: Att)
  extends DefinitionToString with OuterKORE {

  private def allModules(m: Module): Set[Module] = m.importedModules + m

  lazy val modules = entryModules flatMap allModules

  def getModule(name: String): Option[Module] = modules find { case m: Module => m.name == name; case _ => false }

  override def hashCode = mainModule.hashCode

  override def equals(that: Any) = that match {
    case Definition(`mainModule`, `entryModules`, _) => true
    case _ => false
  }
}

trait Sorting {
  def computeSubsortPOSet(sentences: Set[Sentence]) = {
    val subsortRelations: Set[(Sort, Sort)] = sentences collect {
      case Production(klabel, endSort, Seq(NonTerminal(startSort, _)), att) if klabel.isEmpty => (startSort, endSort)
    }

    POSet(subsortRelations)
  }

  def computeOverloadPOSet(subsorts: POSet[Sort], prods: Set[Production]) = {
    def isLessThan(p1: Production, p2: Production): Boolean = {
        p1.klabel.isDefined &&
        p1.klabelAtt == p2.klabelAtt &&
        subsorts.lessThanEq(p1.sort, p2.sort) &&
        p1.nonterminals.size == p2.nonterminals.size &&
        p1.nonterminals.zip(p2.nonterminals).forall(pair => subsorts.lessThanEq(pair._1.sort, pair._2.sort)) &&
        (p1.sort != p2.sort || p1.nonterminals.map(_.sort) != p2.nonterminals.map(_.sort)) &&
        p1 != p2
    }
    val prodsForOverloads = prods.toSeq.filter(_.klabelAtt.isDefined).groupBy(_.klabelAtt)
    val pairs: Iterable[(Production, Production)] = for (x <- prodsForOverloads.values; p1 <- x; p2 <- x; if isLessThan(p1, p2)) yield (p1, p2)
    POSet(pairs.toSet)
  }
}

object Module {
  def apply(name: String, unresolvedLocalSentences: Set[Sentence]): Module = {
    new Module(name, Set(), unresolvedLocalSentences, Att.empty)
  }
}

case class Module(val name: String, val imports: Set[Module], localSentences: Set[Sentence], @(Nonnull@param) val att: Att = Att.empty)
  extends ModuleToString with OuterKORE with Sorting with Serializable {

  assert(att != null)

  private lazy val importedSentences = imports flatMap {_.sentences}

  lazy val sentences: Set[Sentence] = localSentences | importedSentences

  /** All the imported modules, calculated recursively. */
  lazy val importedModules: Set[Module] = imports | (imports flatMap {
    _.importedModules
  })

  lazy val importedModuleNames: Set[String] = importedModules.map(_.name)

  lazy val productions: Set[Production] = sentences collect { case p: Production => p }

  lazy val productionsFor: Map[KLabel, Set[Production]] =
    productions
      .collect({ case p if p.klabel != None => p })
      .groupBy(_.klabel.get)
      .map { case (l, ps) => (l, ps) }

  lazy val productionsForSort: Map[Sort, Set[Production]] =
    productions
      .groupBy(_.sort)
      .map { case (l, ps) => (l, ps) }

  lazy val layouts: Set[String] =
    productionsForSort
      .get(Sorts.Layout)
      .getOrElse(Set[Production]())
      .collect({
          case Production(_, _, Seq(RegexTerminal(_, terminalRegex, _)), _) => terminalRegex
          case p => throw KEMException.compilerError("Productions of sort `Layout` must be exactly one `RegexTerminal`.\nProduction: " + p.toString())
      })

  lazy val layout: String = "(" + layouts.mkString(")|(") + ")"

  @transient
  lazy val definedKLabels: Set[KLabel] =
    (productionsFor.keys.toSet).filter(!_.isInstanceOf[KVariable])

  lazy val klabelsDefinedInRules: Map[KLabel, Int] = {
    def mergeMultiset(map1: Map[KLabel, Int], map2: Map[KLabel, Int]) = map1 ++ map2.map { case (k, v) => k -> (v + map1.getOrElse(k, 0)) }

    val transformer = new FoldK[Map[KLabel, Int]] {
      override def apply(k: KApply): Map[KLabel, Int] = merge(apply(k.klist), Map((k.klabel, 1)))

      override def apply(k: InjectedKLabel): Map[KLabel, Int] = Map((k.klabel, 1))

      def unit = Map()

      def merge(map1: Map[KLabel, Int], map2: Map[KLabel, Int]) = mergeMultiset(map1, map2)
    }
    rules.map(r => {
      mergeMultiset(transformer.apply(r.body), mergeMultiset(transformer.apply(r.requires), transformer.apply(r.ensures)))
    }).fold(Map())(mergeMultiset)
  }

  lazy val tokenProductionsFor: Map[Sort, Set[Production]] =
    productions
      .collect({ case p if p.att.contains("token") => p })
      .groupBy(_.sort)
      .map { case (s, ps) => (s, ps) }

  def tokenProductionFor(s: Sort): Production = {
    if (tokenProductionsFor.contains(s))
      tokenProductionsFor.apply(s).head
    else
      Production(None, s, Seq(), Att.empty.add("token"))
  }


  lazy val bracketProductionsFor: Map[Sort, List[Production]] =
    productions
      .collect({ case p if p.att.contains("bracket") => p })
      .groupBy(_.sort)
      .map { case (s, ps) => (s, ps.toList.sortBy(_.sort)(subsorts.asOrdering)) }

  @transient lazy val sortFor: Map[KLabel, Sort] = productionsFor mapValues {_.head.sort}

  def optionSortFor(k: K): Option[Sort] = k match {
    case Unapply.KApply(l, _) => sortFor.get(l)
    case Unapply.KRewrite(_, r) => optionSortFor(r)
    case Unapply.KToken(_, sort) => Some(sort)
    case Unapply.KSequence(s) => optionSortFor(s.last)
  }

  def isSort(klabel: KLabel, s: Sort) = subsorts.<(sortFor(klabel), s)

  lazy val rules: Set[Rule] = sentences collect { case r: Rule => r }
  lazy val contexts: Set[Context] = sentences collect { case r: Context => r }

  lazy val localRules: Set[Rule] = localSentences collect { case r: Rule => r }

  // Check that productions with the same klabel have identical attributes
  //  productionsFor.foreach {
  //    case (l, ps) =>
  //      if (ps.groupBy(_.att).size != 1)
  //        throw DivergingAttributesForTheSameKLabel(ps)
  //  }

  @transient lazy val attributesFor: Map[KLabel, Att] = productionsFor mapValues {mergeAttributes(_)}

  @transient lazy val signatureFor: Map[KLabel, Set[(Seq[Sort], Sort)]] =
    productionsFor mapValues {
      ps: Set[Production] =>
        ps.map {
          p: Production =>
            val params: Seq[Sort] = p.items collect { case NonTerminal(sort, _) => sort }
            (params, p.sort)
        }
    }

  lazy val sortDeclarations: Set[SyntaxSort] = sentences.collect({ case s: SyntaxSort => s })

  lazy val sortDeclarationsFor: Map[Sort, Set[SyntaxSort]] =
    sortDeclarations
      .groupBy(_.sort)

  @transient lazy val sortAttributesFor: Map[Sort, Att] = sortDeclarationsFor mapValues {mergeAttributes(_)}

  private def mergeAttributes[T <: Sentence](p: Set[T]) = {
    val union = p.flatMap(_.att.att)
    val attMap = union.groupBy({ case ((name, _), _) => name})
    Att(union.filter { key => attMap(key._1._1).size == 1 }.toMap)
  }

  lazy val definedSorts: Set[Sort] = (productions map {_.sort}) ++ (sortDeclarations map {_.sort})
  lazy val usedCellSorts: Set[Sort] = productions.flatMap { p => p.items.collect { case NonTerminal(s, _) => s }
    .filter(s => s.name.endsWith("Cell") || s.name.endsWith("CellFragment"))
  }

  lazy val listSorts: Set[Sort] = sentences.collect({ case Production(_, srt, _, att1) if att1.contains("userList") =>
    srt
  })

  lazy val subsorts: POSet[Sort] = computeSubsortPOSet(sentences)
  lazy val overloads: POSet[Production] = computeOverloadPOSet(subsorts, productions)

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

  @transient lazy val freshFunctionFor: Map[Sort, KLabel] =
    productions.groupBy(_.sort).mapValues(_.filter(_.att.contains("freshGenerator")))
      .filter(_._2.nonEmpty).mapValues(_.map(p => p.klabel.get)).mapValues { set => {
      if (set.size > 1)
        throw KEMException.compilerError("Found more than one fresh generator for sort " + sortFor(set.head)
          + ". Found: " + set)
      else
        set.head
    }
    }

  // check that non-terminals have a defined sort
  def checkSorts () = sentences foreach {
    case p@Production(_, _, items, _) =>
      val res = items collect { case nt: NonTerminal if !definedSorts.contains(nt.sort) && !usedCellSorts.contains(nt.sort) => nt }
      if (res.nonEmpty)
        throw KEMException.compilerError("Could not find sorts: " + res.asJava, p)
    case _ =>
  }

  override lazy val hashCode: Int = name.hashCode

  override def equals(that: Any) = that match {
    case m: Module => m.name == name && m.sentences == sentences
  }
}

// hooked but different from core, Import is a sentence here

trait Sentence extends HasLocation {
  // marker
  val isSyntax: Boolean
  val isNonSyntax: Boolean
  val att: Att
  def withAtt(att: Att): Sentence
  def location: Optional[Location] = att.getOptional(classOf[Location])
  def source: Optional[Source] = att.getOptional(classOf[Source])
}

// deprecated
case class Context(body: K, requires: K, att: Att = Att.empty) extends Sentence with OuterKORE with ContextToString {
  override val isSyntax = false
  override val isNonSyntax = true
  override def withAtt(att: Att) = Context(body, requires, att)
}

case class Rule(body: K, requires: K, ensures: K, att: Att = Att.empty) extends Sentence with RuleToString with OuterKORE {
  override val isSyntax = false
  override val isNonSyntax = true
  override def withAtt(att: Att) = Rule(body, requires, ensures, att)
}

case class ModuleComment(comment: String, att: Att = Att.empty) extends Sentence with OuterKORE {
  override val isSyntax = false
  override val isNonSyntax = true
  override def withAtt(att: Att) = ModuleComment(comment, att)
}

// hooked

// syntax declarations

case class SyntaxPriority(priorities: Seq[Set[Tag]], att: Att = Att.empty)
  extends Sentence with SyntaxPriorityToString with OuterKORE {
  override val isSyntax = true
  override val isNonSyntax = false
  override def withAtt(att: Att) = SyntaxPriority(priorities, att)
}

object Associativity extends Enumeration {
  type Value1 = Value
  val Left, Right, NonAssoc, Unspecified = Value
}

case class SyntaxAssociativity(
                                assoc: Associativity.Value,
                                tags: Set[Tag],
                                att: Att = Att.empty)
  extends Sentence with SyntaxAssociativityToString with OuterKORE {
  override val isSyntax = true
  override val isNonSyntax = false
  override def withAtt(att: Att) = SyntaxAssociativity(assoc, tags, att)
}

case class Tag(name: String) extends TagToString with OuterKORE

//trait Production {
//  def sort: Sort
//  def att: Att
//  def items: Seq[ProductionItem]
//  def klabel: Option[KLabel] =
//    att.get(Production.kLabelAttribute).headOption map { case KList(KToken(s, _, _)) => s } map { KLabel(_) }
//}

case class SyntaxSort(sort: Sort, att: Att = Att.empty) extends Sentence
  with SyntaxSortToString with OuterKORE {
  def items = Seq()

  override val isSyntax = true
  override val isNonSyntax = false
  override def withAtt(att: Att) = SyntaxSort(sort, att)
}

case class Production(klabel: Option[KLabel], sort: Sort, items: Seq[ProductionItem], att: Att)
  extends Sentence with ProductionToString {

  lazy val klabelAtt: Option[String] = att.getOption("klabel")

  override def equals(that: Any) = that match {
    case p@Production(`klabel`, `sort`, `items`, _) => this.att.getOption("poly") == p.att.getOption("poly") && this.att.getOption("function") == p.att.getOption("function")
    case _ => false
  }

  override lazy val hashCode: Int = ((sort.hashCode() * 31 + items.hashCode()) * 31 + klabel.hashCode()) * 31 + att.getOption("poly").hashCode()

  lazy val isSyntacticSubsort: Boolean =
    items.size == 1 && items.head.isInstanceOf[NonTerminal]

  lazy val isSubsort: Boolean =
    isSyntacticSubsort && klabel.isEmpty

  lazy val getSubsortSort: Sort =
    items.head.asInstanceOf[NonTerminal].sort

  lazy val nonterminals = items.filter(_.isInstanceOf[NonTerminal]).map(_.asInstanceOf[NonTerminal])

  lazy val arity: Int = nonterminals.size

  def nonterminal(i: Int): NonTerminal = nonterminals(i)

  private def computePrefixProduction: Boolean = {
    var state = 0
    for (item <- items) {
      if (state == 0) {
        // some sequence of terminals ending in an open parens
        item match {
          case terminal: Terminal if terminal.value == "(" => state = 1
          case _: Terminal =>
          case _ => return false
        }
      } else if (state == 1) {
        // a nonterminal or a close paren
        item match {
          case _: NonTerminal => state = 2
          case terminal: Terminal if terminal.value == ")" => state = 4
          case _ => return false
        }
      } else if (state == 2) {
        // a close paren or a comma
        item match {
          case terminal: Terminal if terminal.value == "," => state = 3
          case terminal: Terminal if terminal.value == ")" => state = 4
          case _ => return false
        }
      } else if (state == 3) {
        // a nonterminal
        item match {
          case _: NonTerminal => state = 2
          case _ => return false
        }
      } else {
        return false
      }
    }
    state == 4
  }

  lazy val isPrefixProduction: Boolean = computePrefixProduction

  private def makeRecordProduction(terminals: Seq[NonTerminal]): Production = {
    val prefix = items.takeWhile(_.isInstanceOf[Terminal]) :+ Terminal("...")
    val suffix = items.last
    val newAtt = att.add("recordPrd", classOf[Production], this).add("unparseAvoid")
    if (terminals.isEmpty)
      Production(klabel, sort, prefix :+ suffix, newAtt)
    else {
      val middle = terminals.tail.foldLeft(Seq(Terminal(terminals.head.name.get), Terminal(":"), terminals.head)){ (l, nt) => l ++ Seq(Terminal(","), Terminal(nt.name.get), Terminal(":"), nt) }
      Production(klabel, sort, prefix ++ middle :+ suffix, newAtt)
    }
  }

  lazy val recordProductions: Set[Production] = {
    assert(isPrefixProduction)
    val namedNts = items.filter(_.isInstanceOf[NonTerminal]).map(_.asInstanceOf[NonTerminal]).filter(_.name.isDefined).toSeq
    val powerSet = 0 to namedNts.size flatMap namedNts.combinations
    powerSet.map(makeRecordProduction).toSet
  }
  override val isSyntax = true
  override val isNonSyntax = false
  override def withAtt(att: Att) = Production(klabel, sort, items, att)
}

object Production {
  def apply(klabel: KLabel, sort: Sort, items: Seq[ProductionItem], att: Att = Att.empty): Production = {
    Production(Some(klabel), sort, items, att)
  }
  def apply(sort: Sort, items: Seq[ProductionItem], att: Att): Production = {
    if (att.contains(kLabelAttribute)) {
      Production(Some(KORE.KLabel(att.get(kLabelAttribute))), sort, items, att)
    } else {
      Production(None, sort, items, att)
    }
  }

  val kLabelAttribute = "klabel"
}

// hooked but problematic, see kast-core.k

sealed trait ProductionItem extends OuterKORE

// marker

sealed trait TerminalLike extends ProductionItem {
}

case class NonTerminal(sort: Sort, name: Option[String]) extends ProductionItem
  with NonTerminalToString

case class RegexTerminal(precedeRegex: String, regex: String, followRegex: String) extends TerminalLike with
  RegexTerminalToString {
  lazy val pattern = new RunAutomaton(new RegExp(regex).toAutomaton, false)
  lazy val followPattern = new RunAutomaton(new RegExp(followRegex).toAutomaton, false)
  lazy val precedePattern = {
    val unreversed = new RegExp(precedeRegex).toAutomaton
    SpecialOperations.reverse(unreversed)
    new RunAutomaton(unreversed, false)
  }
}

case class Terminal(value: String) extends TerminalLike // hooked
  with TerminalToString {
}
