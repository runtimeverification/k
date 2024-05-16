// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework.definition

import dk.brics.automaton.RegExp
import dk.brics.automaton.RunAutomaton
import java.util.Optional
import javax.annotation.Nonnull
import org.kframework.attributes._
import org.kframework.builtin.Sorts
import org.kframework.definition.regex.Regex
import org.kframework.definition.regex.RegexSyntax
import org.kframework.definition.Constructors._
import org.kframework.kore._
import org.kframework.kore.KORE.Sort
import org.kframework.utils.errorsystem.KEMException
import org.kframework.POSet
import scala.annotation.meta.param
import scala.collection.{ IndexedSeq => _ }
import scala.collection.{ Seq => _ }
import scala.collection.immutable
import scala.collection.parallel.CollectionConverters._
import scala.jdk.CollectionConverters._

trait OuterKORE

case class Definition(mainModule: Module, entryModules: immutable.Set[Module], att: Att)
    extends DefinitionToString
    with OuterKORE
    with AttValue {

  private def allModules(m: Module): immutable.Set[Module] = m.importedModules ++ Set(m)

  lazy val modules: immutable.Set[Module] = entryModules.flatMap(allModules)

  def getModule(name: String): Option[Module] = modules.find {
    case m: Module => m.name == name; case _ => false
  }

  override def hashCode: Int = mainModule.hashCode

  override def equals(that: Any): Boolean = that match {
    case Definition(`mainModule`, `entryModules`, _) => true
    case _                                           => false
  }

  def parMap(f: Module => Module): java.util.Map[String, Module] =
    (entryModules | entryModules
      .flatMap(_.importedModules)).par.map(f).seq.map(m => m.name -> m).toMap.asJava
}

trait Sorting {
  def computeSubsortPOSet(sentences: Set[Sentence], syntactic: Boolean): POSet[Sort] = {
    val subsortRelations: Set[(Sort, Sort)] = sentences.collect {
      case Production(klabel, immutable.Seq(), endSort, immutable.Seq(NonTerminal(startSort, _)), _)
          if klabel.isEmpty || syntactic =>
        (startSort, endSort)
    }

    new POSet(subsortRelations)
  }

  /**
   * Let `p` and `q` be the following productions:
   * {{{
   *   P ::= p(P1, ..., PN)
   *   Q ::= q(Q1, ..., QN)
   * }}}
   * Let `<:` be the subsort relation for this definition. We say that `p` is strictly less than `q`
   * with respect to the _overload partial order_ if:
   *   - `p` and `q` are not the same production
   *   - `P <: Q`
   *   - for all n, `Pn <: Qn`
   *   - `p` and `q` are not _identically_ sorted
   * That is, a production `p` is substitutable where a production `q` is expected.
   *
   * This ordering defines which productions participate in overload selection with each other.
   */
  private def isLessThan(p1: Production, p2: Production, subsorts: POSet[Sort]): Boolean =
    p1.nonterminals.size == p2.nonterminals.size &&
      subsorts.lessThanEq(p1.sort, p2.sort) &&
      p1.nonterminals
        .zip(p2.nonterminals)
        .forall(pair => subsorts.lessThanEq(pair._1.sort, pair._2.sort)) &&
      (p1.sort != p2.sort || p1.nonterminals.map(_.sort) != p2.nonterminals.map(_.sort)) &&
      p1 != p2

  /**
   * Compute an overload ordering based on productions with the same `overload(_)` attribute.
   */
  private def computeAttributeOverloadPOSet(
      subsorts: POSet[Sort],
      prods: Set[Production]
  ): Set[(Production, Production)] = {
    val prodsToConsider =
      prods.to(immutable.Seq).filter(_.att.contains(Att.OVERLOAD)).groupBy(_.att.get(Att.OVERLOAD))
    val pairs: Iterable[(Production, Production)] = for {
      x  <- prodsToConsider.values
      p1 <- x
      p2 <- x if isLessThan(p1, p2, subsorts)
    } yield (p1, p2)
    pairs.toSet
  }

  /**
   * Compute an overload ordering based on productions with the same `klabel`. This ordering will be
   * deprecated in the future in favour of the explicit `overload(_)` attribute.
   */
  private def computeKLabelOverloadPOSet(
      subsorts: POSet[Sort],
      prods: Set[Production]
  ): Set[(Production, Production)] = {
    def areKLabelOverloadable(p1: Production, p2: Production): Boolean =
      p1.klabel.isDefined && p1.klabelAtt == p2.klabelAtt && isLessThan(p1, p2, subsorts)

    val prodsForOverloads =
      prods.to(immutable.Seq).filter(_.klabelAtt.isDefined).groupBy(_.klabelAtt)
    val pairs: Iterable[(Production, Production)] = for {
      x  <- prodsForOverloads.values
      p1 <- x
      p2 <- x if areKLabelOverloadable(p1, p2)
    } yield (p1, p2)
    pairs.toSet
  }

  /**
   * Combine the orderings induced by `klabel(_)` and `overload(_)` to produce an overall partial
   * ordering for production overloading.
   *
   * In the future, the `klabel(_)` mechanism will be removed.
   *
   * Note that for now, while the two methods are both supported, we rely here on the compiler
   * rejecting productions that use both attributes to ensure that the two orderings are disjoint.
   */
  def computeOverloadPOSet(
      subsorts: POSet[Sort],
      prods: Set[Production]
  ): POSet[Production] =
    new POSet(
      computeAttributeOverloadPOSet(subsorts, prods) ++ computeKLabelOverloadPOSet(subsorts, prods)
    )

}

object Module {
  def apply(name: String, unresolvedLocalSentences: immutable.Set[Sentence]): Module =
    new Module(name, immutable.Set(), unresolvedLocalSentences, Att.empty)
}

case class Import(module: Module, isPublic: Boolean)

case class Module(
    name: String,
    imports: immutable.Set[Import],
    localSentences: immutable.Set[Sentence],
    @(Nonnull @param) att: Att = Att.empty
) extends ModuleToString
    with OuterKORE
    with Sorting
    with Serializable
    with AttValue
    with HasAtt
    with HasLocation {

  assert(att != null)

  def location: Optional[Location] = att.getOptional(Att.LOCATION, classOf[Location])
  def source: Optional[Source]     = att.getOptional(Att.SOURCE, classOf[Source])

  lazy val fullImports: immutable.Set[Module] = imports.map(_.module)

  private lazy val importedSentences = fullImports.flatMap(_.sentences)

  lazy val sentences: immutable.Set[Sentence] = localSentences | importedSentences

  lazy val sortedLocalSentences: immutable.Seq[Sentence] = localSentences.toSeq.sorted

  lazy val labeled: Map[String, Set[Sentence]] =
    sentences.filter(_.label.isPresent).groupBy(_.label.get)

  /** All the imported modules, calculated recursively. */
  lazy val importedModules: immutable.Set[Module] = fullImports | fullImports.flatMap {
    _.importedModules
  }

  lazy val importedModuleNames: immutable.Set[String] = importedModules.map(_.name)

  lazy val productions: immutable.Set[Production] = sentences.collect { case p: Production => p }

  lazy val publicSentences: immutable.Set[Sentence] =
    if (att.contains(Att.PRIVATE)) {
      localSentences.filter(_.att.contains(Att.PUBLIC))
    } else {
      localSentences.filter(!_.att.contains(Att.PRIVATE))
    }

  lazy val signature: Module = {
    val f = ModuleTransformer.from(
      m => Module(m.name, m.imports.filter(_.isPublic), m.publicSentences, m.att),
      "compute module signature"
    )
    Module(name, imports.map(i => Import(f(i.module), i.isPublic)), localSentences, att)
  }

  lazy val functions: immutable.Set[KLabel] =
    productions.filter(_.att.contains(Att.FUNCTION)).map(_.klabel.get.head)

  def isFunction(t: K): Boolean =
    t match {
      case Unapply.KApply(lbl, _) if functions(lbl)                      => true
      case Unapply.KRewrite(Unapply.KApply(lbl, _), _) if functions(lbl) => true
      case _                                                             => false
    }

  lazy val sortedProductions: immutable.Seq[Production] = productions.to(immutable.Seq).sorted

  lazy val localProductions: immutable.Set[Production] = localSentences.collect {
    case p: Production => p
  }

  lazy val productionsFor: Map[KLabel, immutable.Set[Production]] =
    productions
      .collect { case p if p.klabel.isDefined => p }
      .groupBy(_.klabel.get.head)
      .map { case (l, ps) => (l, ps) }

  lazy val localProductionsFor: Map[KLabel, Set[Production]] =
    localProductions
      .collect { case p if p.klabel.isDefined => p }
      .groupBy(_.klabel.get)
      .map { case (l, ps) => (l, ps) }

  lazy val productionsForSort: Map[SortHead, immutable.Set[Production]] =
    productions
      .groupBy(_.sort.head)
      .map { case (l, ps) => (l, ps) }

  lazy val productionsForLoc: Map[(Source, Location), Set[Production]] =
    productions
      .filter(_.source.isPresent)
      .filter(_.location.isPresent)
      .groupBy(p => (p.source.get, p.location.get))
      .map { case (l, ps) => (l, ps) }

  lazy val layouts: immutable.Set[Regex] =
    productionsForSort
      .getOrElse(Sorts.Layout.head, immutable.Set[Production]())
      .collect {
        case Production(_, _, _, immutable.Seq(RegexTerminal(terminalRegex)), _) =>
          terminalRegex
        case p =>
          throw KEMException.compilerError(
            "Productions of sort `#Layout` must be exactly one `RegexTerminal`.",
            p
          )
      }

  lazy val flexLayout: String =
    "(" + layouts.map(l => RegexSyntax.Flex.print(l)).mkString(")|(") + ")"

  @transient
  lazy val definedKLabels: immutable.Set[KLabel] =
    productionsFor.keys.toSet.filter(!_.isInstanceOf[KVariable]).map(_.head)

  @transient
  lazy val localKLabels: immutable.Set[KLabel] =
    localProductionsFor.keys.toSet.filter(!_.isInstanceOf[KVariable])

  lazy val tokenSorts: immutable.Set[Sort] =
    sentences.collect {
      case p: Production if p.att.contains(Att.TOKEN) => p.sort
      case s: SyntaxSort if s.att.contains(Att.TOKEN) => s.sort
    }

  lazy val tokenProductionsFor: Map[Sort, Set[Production]] =
    productions
      .collect { case p if p.att.contains(Att.TOKEN) => p }
      .groupBy(_.sort)
      .map { case (s, ps) => (s, ps) }

  def tokenProductionFor(s: Sort): Production =
    if (tokenProductionsFor.contains(s))
      tokenProductionsFor.apply(s).head
    else
      Production(None, immutable.Seq(), s, immutable.Seq(), Att.empty.add(Att.TOKEN))

  lazy val allModuleNames: immutable.Set[String] = importedModuleNames ++ Set(name)

  def importedSentencesExcept(m: Module): immutable.Set[Sentence] =
    importedModules.flatMap { i =>
      if (m.allModuleNames contains i.name) Set.empty[Sentence] else i.localSentences
    }
  def sentencesExcept(m: Module): immutable.Set[Sentence] =
    importedSentencesExcept(m) | localSentences

  lazy val bracketProductionsFor: Map[Sort, List[Production]] =
    productions
      .collect { case p if p.att.contains(Att.BRACKET) => p }
      .groupBy(_.sort)
      .map { case (s, ps) =>
        (
          s,
          ps.toList.sortBy(_.sort)(
            scala.math.Ordering.comparatorToOrdering(subsorts.asComparator())
          )
        )
      }

  @transient lazy val sortFor: Map[KLabel, Sort] = productionsFor.view.mapValues(_.head.sort).toMap

  lazy val claims: immutable.Set[Claim]     = sentences.collect { case c: Claim => c }
  lazy val rules: immutable.Set[Rule]       = sentences.collect { case r: Rule => r }
  lazy val rulesFor: Map[KLabel, Set[Rule]] = rules.groupBy(r => matchKLabel(r))
  lazy val macroKLabels: immutable.Set[KLabel] =
    macroKLabelsFromRules ++ macroKLabelsFromProductions
  lazy val macroKLabelsFromRules: immutable.Set[KLabel] =
    rules.filter(r => r.isMacro).map(r => matchKLabel(r))
  lazy val macroKLabelsFromProductions: immutable.Set[KLabel] =
    productions.filter(p => p.isMacro).map(p => matchKLabel(p))

  def matchKLabel(r: Rule): KLabel = r.body match {
    case Unapply.KApply(Unapply.KLabel("#withConfig"), Unapply.KApply(s, _) :: _) => s
    case Unapply.KApply(
          Unapply.KLabel("#withConfig"),
          Unapply.KRewrite(Unapply.KApply(s, _), _) :: _
        ) =>
      s
    case Unapply.KApply(s, _)                      => s
    case Unapply.KRewrite(Unapply.KApply(s, _), _) => s
    case _                                         => KORE.KLabel("")
  }

  private def matchKLabel(p: Production) = p.klabel match {
    case Some(klabel) => klabel
    case _            => KORE.KLabel("")
  }

  def ruleLhsHasMacroKLabel(r: Rule): Boolean = r.body match {
    case Unapply.KRewrite(Unapply.KApply(l @ Unapply.KLabel(_), _), _) =>
      macroKLabelsFromProductions.contains(l)
    case _ => false
  }

  lazy val contexts: immutable.Set[Context] = sentences.collect { case r: Context => r }

  lazy val sortedRules: immutable.Seq[Rule] = rules.to(immutable.Seq).sorted

  lazy val localRules: immutable.Set[Rule]   = localSentences.collect { case r: Rule => r }
  lazy val localClaims: immutable.Set[Claim] = localSentences.collect { case r: Claim => r }

  // Check that productions with the same klabel have identical attributes
  //  productionsFor.foreach {
  //    case (l, ps) =>
  //      if (ps.groupBy(_.att).size != 1)
  //        throw DivergingAttributesForTheSameKLabel(ps)
  //  }

  @transient lazy val attributesFor: Map[KLabel, Att] = productionsFor.view.mapValues {
    mergeAttributes
  }.toMap

  @transient lazy val signatureFor: Map[KLabel, Set[(immutable.Seq[Sort], Sort)]] =
    productionsFor.view.mapValues { ps: immutable.Set[Production] =>
      ps.filter { p: Production => p.params.isEmpty }
        .map { p: Production =>
          val params: immutable.Seq[Sort] = p.items.collect { case NonTerminal(sort, _) => sort }
          (params, p.sort)
        }
    }.toMap

  lazy val sortDeclarations: immutable.Set[SyntaxSort] = sentences.collect { case s: SyntaxSort =>
    s
  }
  lazy val sortSynonyms: immutable.Set[SortSynonym] = sentences.collect { case s: SortSynonym => s }
  lazy val lexicalIdentifiers: immutable.Set[SyntaxLexical] = sentences.collect {
    case s: SyntaxLexical => s
  }

  lazy val sortSynonymMap: Map[Sort, Sort] = sortSynonyms.map(s => (s.newSort, s.oldSort)).toMap

  lazy val sortDeclarationsFor: Map[SortHead, immutable.Set[SyntaxSort]] =
    (sortDeclarations ++ allSorts.map(s => SyntaxSort(immutable.Seq(), s, Att.empty)))
      .groupBy(_.sort.head)

  @transient lazy val sortAttributesFor: Map[SortHead, Att] = sortDeclarationsFor.view.mapValues {
    mergeAttributes
  }.toMap

  lazy val hookAttributes: Map[String, String] =
    sortAttributesFor.flatMap(s => s._2.getOption(Att.HOOK).map(att => s._1.name -> att))

  private def mergeAttributes[T <: Sentence](p: immutable.Set[T]) =
    Att.mergeAttributes(p.map(_.att))

  lazy val definedSorts: immutable.Set[SortHead] = productions
    .filter(p => !p.isSortVariable(p.sort))
    .map(_.sort.head) ++ (sortDeclarations.filter(s => s.params.isEmpty).map {
    _.sort.head
  }) ++ definedInstantiations.values.flatten.flatMap(_.params).filter(_.isNat).map(_.head)
  lazy val definedInstantiations: Map[SortHead, immutable.Set[Sort]] = {
    val nonempty = ((productions
      .filter { p =>
        p.sort.params.nonEmpty && !p.params
          .contains(p.sort) && (p.sort.params.toSet & p.params.toSet).isEmpty
      }
      .map(_.sort)) ++ (sortDeclarations
      .filter(s => s.params.isEmpty && s.sort.params.nonEmpty)
      .map(_.sort))).groupBy(_.head)
    ((productions.filter(p => p.sort.params.nonEmpty).map(_.sort.head)) ++ (sortDeclarations
      .filter(s => s.sort.params.nonEmpty)
      .map(_.sort.head))).map(s => s -> nonempty.getOrElse(s, immutable.Set())).toMap
  }
  lazy val allSorts: immutable.Set[Sort] = (definedSorts -- definedInstantiations.keys).map(
    Sort
  ) ++ definedInstantiations.values.flatten
  lazy val localSorts: immutable.Set[Sort]             = allSorts -- fullImports.flatMap(_.allSorts)
  lazy val sortedDefinedSorts: immutable.Seq[SortHead] = definedSorts.to(immutable.Seq).sorted
  lazy val sortedAllSorts: immutable.Seq[Sort]         = allSorts.to(immutable.Seq).sorted

  lazy val listSorts: immutable.Set[Sort] = sentences.collect {
    case Production(_, _, srt, _, att1) if att1.contains(Att.USER_LIST) =>
      srt
  }

  lazy val subsorts: POSet[Sort]          = computeSubsortPOSet(sentences, false)
  lazy val syntacticSubsorts: POSet[Sort] = computeSubsortPOSet(sentences, true)
  lazy val overloads: POSet[Production]   = computeOverloadPOSet(subsorts, productions)

  private lazy val expressedPriorities: immutable.Set[(Tag, Tag)] =
    sentences
      .collect { case SyntaxPriority(ps, _) => ps }
      .flatMap { ps: immutable.Seq[Set[Tag]] =>
        val pairSetAndPenultimateTagSet = ps.foldLeft((Set[(Tag, Tag)](), Set[Tag]())) {
          case ((all, prev), current) =>
            val newPairs = for {
              a <- prev
              b <- current
            } yield (a, b)

            (newPairs | all, current)
        }
        pairSetAndPenultimateTagSet._1 // we're only interested in the pair set part of the fold
      }
  lazy val priorities = new POSet[Tag](expressedPriorities)
  lazy val leftAssoc  = buildAssoc(Associativity.Left)
  lazy val rightAssoc = buildAssoc(Associativity.Right)

  private def buildAssoc(side: Associativity): Set[(Tag, Tag)] =
    sentences
      .collect { case SyntaxAssociativity(`side` | Associativity.NonAssoc, ps, _) => ps }
      .flatMap { ps: Set[Tag] =>
        for {
          a <- ps
          b <- ps
        } yield (a, b)
      }

  @transient lazy val freshFunctionFor: Map[Sort, KLabel] =
    productions
      .groupBy(_.sort)
      .view
      .mapValues(_.filter(_.att.contains(Att.FRESH_GENERATOR)))
      .filter(_._2.nonEmpty)
      .view
      .mapValues(_.map(p => p.klabel.get))
      .mapValues { set =>
        if (set.size > 1)
          throw KEMException.compilerError(
            "Found more than one fresh generator for sort " + sortFor(set.head)
              + ". Found: " + set
          )
        else
          set.head
      }
      .toMap

  private def throwIfUserParametricSort(sort: Sort, loc: HasLocation): Unit =
    if (sort.head.params != 0 && sort.name != Sorts.MInt.name)
      throw KEMException.compilerError(
        "User-defined parametric sorts are currently " +
          "unsupported: " + sort,
        loc
      )

  // Check that user-defined sorts are non-parametric and that
  // each non-terminal has a defined sort
  def checkSorts(): Unit = localSentences.foreach {
    case s @ SyntaxSort(_, sort, _)     => throwIfUserParametricSort(sort, s)
    case s @ SortSynonym(newSort, _, _) => throwIfUserParametricSort(newSort, s)
    case p @ Production(_, params, sort, items, _) =>
      throwIfUserParametricSort(sort, p)
//      val parFun: PartialFunction[ProductionItem, Sort] = {
//        case nt: NonTerminal
//            if !p.isSortVariable(nt.sort) && !definedSorts.contains(nt.sort.head) && !sortSynonymMap
//              .contains(nt.sort) =>
//          nt.sort: org.kframework.kore.Sort
//        case nt: NonTerminal
//            if nt.sort.params.nonEmpty && (nt.sort.params.toSet & params.toSet).isEmpty && !definedInstantiations
//              .getOrElse(nt.sort.head, Set())
//              .contains(nt.sort) =>
//          nt.sort: org.kframework.kore.Sort
//      }
      val res: immutable.Seq[Sort] = items
        .collect { case nt: NonTerminal => nt }
        .filter(nt =>
          (!p.isSortVariable(nt.sort) && !definedSorts.contains(nt.sort.head) && !sortSynonymMap
            .contains(
              nt.sort
            )) || (nt.sort.params.nonEmpty && (nt.sort.params.toSet & params.toSet).isEmpty && !definedInstantiations
            .getOrElse(nt.sort.head, immutable.Set())
            .contains(nt.sort))
        )
        .map(nt => nt.sort)
        .to(immutable.Seq)
      if (res.nonEmpty)
        throw KEMException.compilerError("Could not find sorts: " + res.asJava, p)
    case _ =>
  }

  def checkUserLists(): Unit = localSentences.foreach {
    case p @ Production(_, _, srt, _, atts) =>
      if (atts.contains(Att.USER_LIST)) {
        val prev = sentences.find(s =>
          s.isInstanceOf[Production]
            && s.asInstanceOf[Production].sort.equals(srt)
            && s.att.contains(Att.USER_LIST)
            && !(s.source.equals(p.source)
              && s.location.equals(p.location))
        )
        if (prev.isDefined)
          throw KEMException.compilerError(
            "Sort " + srt + " previously declared as a user list at "
              + prev.get.source.get() + " and "
              + prev.get.location.get(),
            p
          )
      }
    case _ =>
  }

  lazy val recordProjections = productions.flatMap(p =>
    p.nonterminals
      .filter(_.name.isDefined)
      .map(nt => "project:" ++ p.klabel.get.name ++ ":" ++ nt.name.get)
  )
  lazy val semanticCasts   = allSorts.map("#SemanticCastTo" + _)
  lazy val sortProjections = allSorts.map("project:" + _)
  lazy val sortPredicates  = allSorts.map("is" + _)

  override lazy val hashCode: Int = name.hashCode

  def flattened(): FlatModule = new FlatModule(
    name,
    imports.map(i => FlatImport(i.module.name, i.isPublic, Att.empty)),
    localSentences,
    att
  )
  def flatModules(): (String, Set[FlatModule]) =
    (name, Set(flattened()) ++ fullImports.flatMap(m => m.flatModules()._2))
}

trait HasAtt {
  val att: Att
  def isMacro: Boolean = att.contains(Att.MACRO) || att.contains(Att.MACRO_REC) || att.contains(
    Att.ALIAS
  ) || att.contains(Att.ALIAS_REC)
}

trait Sentence extends HasLocation with HasAtt with AttValue {
  // marker
  val isSyntax: Boolean
  val isNonSyntax: Boolean
  val att: Att
  def withAtt(att: Att): Sentence
  def location: Optional[Location] = att.getOptional(Att.LOCATION, classOf[Location])
  def source: Optional[Source]     = att.getOptional(Att.SOURCE, classOf[Source])
  def label: Optional[String]      = att.getOptional(Att.LABEL)
}

object Sentence {
  implicit val ord: Ordering[Sentence] = (a: Sentence, b: Sentence) =>
    (a, b) match {
      case (c: SyntaxSort, d: SyntaxSort)       => Ordering[SyntaxSort].compare(c, d)
      case (c: SortSynonym, d: SortSynonym)     => Ordering[SortSynonym].compare(c, d)
      case (c: SyntaxLexical, d: SyntaxLexical) => Ordering[SyntaxLexical].compare(c, d)
      case (c: Production, d: Production)       => Ordering[Production].compare(c, d)
      case (c: SyntaxAssociativity, d: SyntaxAssociativity) =>
        Ordering[SyntaxAssociativity].compare(c, d)
      case (c: SyntaxPriority, d: SyntaxPriority) => Ordering[SyntaxPriority].compare(c, d)
      case (c: ContextAlias, d: ContextAlias)     => Ordering[ContextAlias].compare(c, d)
      case (c: Context, d: Context)               => Ordering[Context].compare(c, d)
      case (c: Rule, d: Rule)                     => Ordering[Rule].compare(c, d)
      case (c: Claim, d: Claim)                   => Ordering[Claim].compare(c, d)
      case (_: SyntaxSort, _)                     => -1
      case (_, _: SyntaxSort)                     => 1
      case (_: SortSynonym, _)                    => -1
      case (_, _: SortSynonym)                    => 1
      case (_: SyntaxLexical, _)                  => -1
      case (_, _: SyntaxLexical)                  => 1
      case (_: Production, _)                     => -1
      case (_, _: Production)                     => 1
      case (_: SyntaxAssociativity, _)            => -1
      case (_, _: SyntaxAssociativity)            => 1
      case (_: SyntaxPriority, _)                 => -1
      case (_, _: SyntaxPriority)                 => 1
      case (_: ContextAlias, _)                   => -1
      case (_, _: ContextAlias)                   => 1
      case (_: Context, _)                        => -1
      case (_, _: Context)                        => 1
      case (_: Rule, _)                           => -1
      case (_, _: Rule)                           => 1
      case (_: Claim, _)                          => -1
      case (_, _: Claim)                          => 1
      case (_, _) =>
        throw KEMException.internalError(
          "Cannot order these sentences:\n" + a.toString() + "\n" + b.toString()
        )
    }
}

// deprecated
case class Context(body: K, requires: K, att: Att = Att.empty)
    extends Sentence
    with OuterKORE
    with ContextToString {
  override val isSyntax          = false
  override val isNonSyntax       = true
  override def withAtt(att: Att) = Context(body, requires, att)
}
object Context {
  implicit val ord: Ordering[Context] =
    Ordering.by[Context, (K, K, Att)](s => (s.body, s.requires, s.att))
}

case class ContextAlias(body: K, requires: K, att: Att = Att.empty)
    extends Sentence
    with OuterKORE
    with ContextAliasToString {
  override val isSyntax          = true
  override val isNonSyntax       = false
  override def withAtt(att: Att) = ContextAlias(body, requires, att)
}
object ContextAlias {
  implicit val ord: Ordering[ContextAlias] =
    Ordering.by[ContextAlias, (K, K, Att)](s => (s.body, s.requires, s.att))
}

abstract class RuleOrClaim extends Sentence {
  def body: K
  def requires: K
  def ensures: K
  override val isSyntax    = false
  override val isNonSyntax = true
  def newInstance(body: K, requires: K, ensures: K, att: Att = Att.empty): RuleOrClaim
}

case class Claim(body: K, requires: K, ensures: K, att: Att = Att.empty)
    extends RuleOrClaim
    with ClaimToString
    with OuterKORE {
  override def withAtt(att: Att): Claim = Claim(body, requires, ensures, att)
  override def newInstance(body: K, requires: K, ensures: K, att: Att = Att.empty): Claim =
    Claim(body, requires, ensures, att)
}
object Claim {
  implicit val ord: Ordering[Claim] =
    Ordering.by[Claim, (K, K, K, Att)](s => (s.body, s.requires, s.ensures, s.att))
}

case class Rule(body: K, requires: K, ensures: K, att: Att = Att.empty)
    extends RuleOrClaim
    with RuleToString
    with OuterKORE {
  override def withAtt(att: Att): Rule = Rule(body, requires, ensures, att)
  override def newInstance(body: K, requires: K, ensures: K, att: Att = Att.empty): Rule =
    Rule(body, requires, ensures, att)
}

object Rule {
  implicit val ord: Ordering[Rule] =
    Ordering.by[Rule, (K, K, K, Att)](r => (r.body, r.requires, r.ensures, r.att))
}

// hooked

// syntax declarations

case class SyntaxPriority(priorities: immutable.Seq[Set[Tag]], att: Att = Att.empty)
    extends Sentence
    with SyntaxPriorityToString
    with OuterKORE {
  override val isSyntax          = true
  override val isNonSyntax       = false
  override def withAtt(att: Att) = SyntaxPriority(priorities, att)
}
object SyntaxPriority {
  implicit val ord: Ordering[SyntaxPriority] = {
    import scala.math.Ordering.Implicits._
    Ordering.by[SyntaxPriority, (immutable.Seq[immutable.Seq[Tag]], Att)](s =>
      (s.priorities.map(_.to(immutable.Seq).sorted), s.att)
    )
  }
}

case class SyntaxAssociativity(assoc: Associativity, tags: Set[Tag], att: Att = Att.empty)
    extends Sentence
    with SyntaxAssociativityToString
    with OuterKORE {
  override val isSyntax          = true
  override val isNonSyntax       = false
  override def withAtt(att: Att) = SyntaxAssociativity(assoc, tags, att)
}
object SyntaxAssociativity {
  implicit val ord: Ordering[SyntaxAssociativity] = {
    import scala.math.Ordering.Implicits._
    Ordering.by[SyntaxAssociativity, (Associativity, immutable.Seq[Tag], Att)](s =>
      (s.assoc, s.tags.to(immutable.Seq).sorted, s.att)
    )
  }
}

case class Tag(name: String) extends TagToString with OuterKORE

object Tag {
  implicit val ord: Ordering[Tag] = Ordering.by[Tag, String](_.name)
}

//trait Production {
//  def sort: Sort
//  def att: Att
//  def items: immutable.Seq[ProductionItem]
//  def klabel: Option[KLabel] =
//    att.get(Production.kLabelAttribute).headOption map { case KList(KToken(s, _, _)) => s } map { KLabel(_) }
//}

case class SyntaxSort(params: immutable.Seq[Sort], sort: Sort, att: Att = Att.empty)
    extends Sentence
    with SyntaxSortToString
    with OuterKORE {
  def items = immutable.Seq()

  override val isSyntax          = true
  override val isNonSyntax       = false
  override def withAtt(att: Att) = SyntaxSort(params, sort, att)
}
object SyntaxSort {
  implicit val ord: Ordering[SyntaxSort] = {
    import scala.math.Ordering.Implicits._
    Ordering.by[SyntaxSort, (immutable.Seq[String], String, Att)](s =>
      (s.params.map(_.name), s.sort.name, s.att)
    )
  }
}

case class SortSynonym(newSort: Sort, oldSort: Sort, att: Att = Att.empty)
    extends Sentence
    with SortSynonymToString
    with OuterKORE {

  override val isSyntax          = true
  override val isNonSyntax       = false
  override def withAtt(att: Att) = SortSynonym(newSort, oldSort, att)
}
object SortSynonym {
  implicit val ord: Ordering[SortSynonym] =
    Ordering.by[SortSynonym, (String, String, Att)](s => (s.newSort.name, s.oldSort.name, s.att))
}

case class SyntaxLexical(name: String, regex: Regex, att: Att = Att.empty)
    extends Sentence
    with SyntaxLexicalToString
    with OuterKORE {

  override val isSyntax          = true
  override val isNonSyntax       = false
  override def withAtt(att: Att) = SyntaxLexical(name, regex, att)
}
object SyntaxLexical {
  implicit val ord: Ordering[SyntaxLexical] =
    Ordering.by[SyntaxLexical, (String, String, Att)](s =>
      (s.name, RegexSyntax.K.print(s.regex), s.att)
    )
}

case class Production(
    klabel: Option[KLabel],
    params: immutable.Seq[Sort],
    sort: Sort,
    items: immutable.Seq[ProductionItem],
    att: Att
) extends Sentence
    with ProductionToString {

  lazy val klabelAtt: Option[String] = att.getOption(Att.KLABEL).orElse(klabel.map(_.name))
  lazy val parseLabel: KLabel        = klabel.getOrElse(att.get(Att.BRACKET_LABEL, classOf[KLabel]))

  override def equals(that: Any): Boolean = that match {
    case p @ Production(`klabel`, `params`, `sort`, `items`, _) => (
      this.klabelAtt == p.klabelAtt
      && this.att.getOption(Att.FUNCTION) == p.att.getOption(Att.FUNCTION)
      && this.att.getOption(Att.SYMBOL) == p.att.getOption(Att.SYMBOL)
    )
    case _ => false
  }

  override lazy val hashCode: Int =
    ((sort.hashCode() * 31 + items.hashCode()) * 31 + klabel.hashCode() * 31) + params.hashCode()

  lazy val isSyntacticSubsort: Boolean =
    items.size == 1 && items.head.isInstanceOf[NonTerminal]

  lazy val isSubsort: Boolean =
    isSyntacticSubsort && klabel.isEmpty

  lazy val getSubsortSort: Sort =
    items.head.asInstanceOf[NonTerminal].sort

  lazy val nonterminals = items.filter(_.isInstanceOf[NonTerminal]).map(_.asInstanceOf[NonTerminal])

  lazy val arity: Int = nonterminals.size

  def nonterminal(i: Int): NonTerminal = nonterminals(i)

  def substitute(args: immutable.Seq[Sort]): Production = {
    val subst = params.zip(args).toMap
    Production(
      klabel.map(l => ADT.KLabel(l.name, args: _*)),
      immutable.Seq(),
      subst.getOrElse(sort, sort.substitute(subst)),
      items.map {
        case NonTerminal(sort, name) =>
          NonTerminal(subst.getOrElse(sort, sort.substitute(subst)), name)
        case i => i
      },
      att
    )
  }

  def isSortVariable(s: Sort): Boolean =
    params.contains(s)

  private def computePrefixProduction: Boolean = {
    var state = 0
    for (item <- items)
      if (state == 0) {
        // some sequence of terminals ending in an open parens
        item match {
          case terminal: Terminal if terminal.value == "(" => state = 1
          case _: Terminal                                 =>
          case _                                           => return false
        }
      } else if (state == 1) {
        // a nonterminal or a close paren
        item match {
          case _: NonTerminal                              => state = 2
          case terminal: Terminal if terminal.value == ")" => state = 4
          case _                                           => return false
        }
      } else if (state == 2) {
        // a close paren or a comma
        item match {
          case terminal: Terminal if terminal.value == "," => state = 3
          case terminal: Terminal if terminal.value == ")" => state = 4
          case _                                           => return false
        }
      } else if (state == 3) {
        // a nonterminal
        item match {
          case _: NonTerminal => state = 2
          case _              => return false
        }
      } else {
        return false
      }
    state == 4
  }

  lazy val isPrefixProduction: Boolean = computePrefixProduction

  /**
   * Generate lists to parse record productions efficiently syntax S ::= prefix(... Uid) [main]
   * syntax Uid ::= "" [empty] syntax Uid ::= UidNe [subsort] syntax UidNe ::= UidNe "," UidItem
   * [repeat] syntax UidNe ::= UidItem [subsort2] syntax UidItem ::= "name" ":" Sort [item]
   */
  def recordProductions(uid: UidProvider): immutable.Set[Production] = {
    assert(isPrefixProduction)
    val namedNts = items
      .filter(_.isInstanceOf[NonTerminal])
      .map(_.asInstanceOf[NonTerminal])
      .filter(_.name.isDefined)
    val prefix = items.takeWhile(_.isInstanceOf[Terminal]) :+ Terminal("...")
    val suffix = items.last
    val newAtt = Att.empty.add(Att.RECORD_PRD, classOf[Production], this)
    if (namedNts.isEmpty)
      // if it doesn't contain named NTs, don't generate the extra list productions
      immutable.Set(
        Production(klabel, params, sort, prefix :+ suffix, newAtt.add(Att.RECORD_PRD_ZERO))
      )
    else if (namedNts.size == 1) {
      val main = Production(klabel, params, sort, prefix :+ suffix, newAtt.add(Att.RECORD_PRD_ZERO))
      val one = Production(
        klabel,
        params,
        sort,
        prefix :+ Terminal(namedNts.head.name.get) :+ Terminal(":") :+ namedNts.head :+ suffix,
        newAtt.add(Att.RECORD_PRD_ONE, namedNts.head.name.get)
      )
      immutable.Set(main, one)
    } else {
      val baseName = items.head.asInstanceOf[Terminal].value + "-" + uid
      val main = Production(
        klabel,
        params,
        sort,
        prefix :+ NonTerminal(Sort(baseName), None) :+ suffix,
        newAtt.add(Att.RECORD_PRD_MAIN)
      )
      val empty = Production(
        klabel,
        immutable.Seq(),
        Sort(baseName),
        immutable.Seq(Terminal("")),
        newAtt.add(Att.RECORD_PRD_EMPTY)
      )
      val subsort = Production(
        None,
        immutable.Seq(),
        Sort(baseName),
        immutable.Seq(NonTerminal(Sort(baseName + "Ne"), None)),
        newAtt.add(Att.RECORD_PRD_SUBSORT)
      )
      val repeat = Production(
        klabel,
        immutable.Seq(),
        Sort(baseName + "Ne"),
        immutable.Seq(
          NonTerminal(Sort(baseName + "Ne"), None),
          Terminal(","),
          NonTerminal(Sort(baseName + "Item"), None)
        ),
        newAtt.add(Att.RECORD_PRD_REPEAT)
      )
      val subsort2 = Production(
        None,
        immutable.Seq(),
        Sort(baseName + "Ne"),
        immutable.Seq(NonTerminal(Sort(baseName + "Item"), None)),
        newAtt.add(Att.RECORD_PRD_SUBSORT)
      )
      val namedItems: immutable.Set[Production] = namedNts
        .map(nt =>
          Production(
            klabel,
            immutable.Seq(),
            Sort(baseName + "Item"),
            immutable.Seq(Terminal(nt.name.get), Terminal(":"), NonTerminal(nt.sort, None)),
            newAtt.add(Att.RECORD_PRD_ITEM, nt.name.get)
          )
        )
        .toSet
      namedItems + main + empty + subsort + repeat + subsort2
    }
  }
  override val isSyntax          = true
  override val isNonSyntax       = false
  override def withAtt(att: Att) = Production(klabel, params, sort, items, att)

  lazy val defaultFormat: String =
    if (isPrefixProduction && nonterminals.size > 0 && nonterminals.forall(_.name.isDefined)) {
      items.zipWithIndex
        .map {
          case (Terminal("("), i)              => s"%${i + 1}..."
          case (Terminal(_), i)                => s"%${i + 1}"
          case (NonTerminal(_, Some(name)), i) => s"$name: %${i + 1}"
          case (RegexTerminal(_), _) =>
            throw new IllegalArgumentException(
              "Default format not supported for productions with regex terminals"
            )
          case _ => throw new AssertionError()
        }
        .mkString(" ")
    } else {
      items.zipWithIndex.map { case (_, i) => s"%${i + 1}" }.mkString(" ")
    }
}

object Production {
  implicit val ord: Ordering[Production] =
    Ordering.by[Production, (Option[String], Att)](s => (s.klabel.map(_.name), s.att))

  def apply(
      klabel: KLabel,
      params: immutable.Seq[Sort],
      sort: Sort,
      items: immutable.Seq[ProductionItem],
      att: Att = Att.empty
  ): Production =
    Production(Some(klabel), params, sort, items, att)
  def apply(
      params: immutable.Seq[Sort],
      sort: Sort,
      items: immutable.Seq[ProductionItem],
      att: Att
  ): Production =
    if (att.contains(Att.KLABEL)) {
      Production(Some(KORE.KLabel(att.get(Att.KLABEL))), params, sort, items, att)
    } else {
      Production(None, params, sort, items, att)
    }
}

// a way to deterministically generate unique IDs dependent on module name
case class UidProvider(modName: String) {
  private var uid               = 0
  override def toString: String = { uid = uid + 1; modName + "+" + uid }
}

// hooked but problematic, see kast-core.k

sealed trait ProductionItem extends OuterKORE

// marker

sealed trait TerminalLike extends ProductionItem with Comparable[TerminalLike] {}

case class NonTerminal(sort: Sort, name: Option[String])
    extends ProductionItem
    with NonTerminalToString

case class RegexTerminal(regex: Regex) extends TerminalLike with RegexTerminalToString {
  lazy val pattern = new RunAutomaton(new RegExp(RegexSyntax.K.print(regex)).toAutomaton, false)

  def compareTo(t: TerminalLike): Int = {
    if (t.isInstanceOf[Terminal]) {
      return 1;
    }
    RegexSyntax.K.print(regex).compareTo(RegexSyntax.K.print(t.asInstanceOf[RegexTerminal].regex))
  }
}

case class Terminal(value: String)
    extends TerminalLike // hooked
    with TerminalToString {

  def compareTo(t: TerminalLike): Int = {
    if (t.isInstanceOf[RegexTerminal]) {
      return -1;
    }
    value.compareTo(t.asInstanceOf[Terminal].value)
  }
}
