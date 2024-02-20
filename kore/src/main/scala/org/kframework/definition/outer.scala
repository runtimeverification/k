// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework.definition

import dk.brics.automaton.RegExp
import dk.brics.automaton.RunAutomaton
import java.util.Optional
import javax.annotation.Nonnull
import org.kframework.attributes._
import org.kframework.builtin.Sorts
import org.kframework.definition.Constructors._
import org.kframework.kore._
import org.kframework.kore.KORE.Sort
import org.kframework.utils.errorsystem.KEMException
import org.kframework.POSet
import scala.annotation.meta.param
import scala.collection._
import scala.collection.JavaConverters._
import scala.collection.Set

trait OuterKORE

case class Definition(mainModule: Module, entryModules: Set[Module], att: Att)
    extends DefinitionToString
    with OuterKORE
    with AttValue {

  private def allModules(m: Module): Set[Module] = m.importedModules + m

  lazy val modules = entryModules.flatMap(allModules)

  def getModule(name: String): Option[Module] = modules.find {
    case m: Module => m.name == name; case _ => false
  }

  override def hashCode = mainModule.hashCode

  override def equals(that: Any) = that match {
    case Definition(`mainModule`, `entryModules`, _) => true
    case _                                           => false
  }

  def parMap(f: Module => Module): java.util.Map[String, Module] =
    (entryModules | entryModules
      .flatMap(_.importedModules)).par.map(f).seq.map(m => m.name -> m).toMap.asJava
}

trait Sorting {
  def computeSubsortPOSet(sentences: Set[Sentence], syntactic: Boolean) = {
    val subsortRelations: Set[(Sort, Sort)] = sentences.collect {
      case Production(klabel, Seq(), endSort, Seq(NonTerminal(startSort, _)), _)
          if klabel.isEmpty || syntactic =>
        (startSort, endSort)
    }

    POSet(subsortRelations)
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
      prods.toSeq.filter(_.att.contains(Att.OVERLOAD)).groupBy(_.att.get(Att.OVERLOAD))
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

    val prodsForOverloads = prods.toSeq.filter(_.klabelAtt.isDefined).groupBy(_.klabelAtt)
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
    POSet(
      computeAttributeOverloadPOSet(subsorts, prods) ++ computeKLabelOverloadPOSet(subsorts, prods)
    )

}

object Module {
  def apply(name: String, unresolvedLocalSentences: Set[Sentence]): Module =
    new Module(name, Set(), unresolvedLocalSentences, Att.empty)
}

case class Import(val module: Module, val isPublic: Boolean)

case class Module(
    val name: String,
    val imports: Set[Import],
    localSentences: Set[Sentence],
    @(Nonnull @param) val att: Att = Att.empty
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

  lazy val fullImports: Set[Module] = imports.map(_.module)

  private lazy val importedSentences = fullImports.flatMap(_.sentences)

  lazy val sentences: Set[Sentence] = localSentences | importedSentences

  lazy val labeled: Map[String, Set[Sentence]] =
    sentences.filter(_.label.isPresent).groupBy(_.label.get)

  /** All the imported modules, calculated recursively. */
  lazy val importedModules: Set[Module] = fullImports | (fullImports.flatMap {
    _.importedModules
  })

  lazy val importedModuleNames: Set[String] = importedModules.map(_.name)

  lazy val productions: Set[Production] = sentences.collect { case p: Production => p }

  lazy val publicSentences: Set[Sentence] =
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

  lazy val functions: Set[KLabel] =
    productions.filter(_.att.contains(Att.FUNCTION)).map(_.klabel.get.head)

  def isFunction(t: K): Boolean =
    t match {
      case Unapply.KApply(lbl, _) if functions(lbl)                      => true
      case Unapply.KRewrite(Unapply.KApply(lbl, _), _) if functions(lbl) => true
      case _                                                             => false
    }

  lazy val sortedProductions: Seq[Production] = productions.toSeq.sorted

  lazy val localProductions: Set[Production] = localSentences.collect { case p: Production => p }

  lazy val productionsFor: Map[KLabel, Set[Production]] =
    productions
      .collect { case p if p.klabel != None => p }
      .groupBy(_.klabel.get.head)
      .map { case (l, ps) => (l, ps) }

  lazy val localProductionsFor: Map[KLabel, Set[Production]] =
    localProductions
      .collect { case p if p.klabel != None => p }
      .groupBy(_.klabel.get)
      .map { case (l, ps) => (l, ps) }

  lazy val productionsForSort: Map[SortHead, Set[Production]] =
    productions
      .groupBy(_.sort.head)
      .map { case (l, ps) => (l, ps) }

  lazy val productionsForLoc: Map[(Source, Location), Set[Production]] =
    productions
      .filter(_.source.isPresent)
      .filter(_.location.isPresent)
      .groupBy(p => (p.source.get, p.location.get))
      .map { case (l, ps) => (l, ps) }

  lazy val layouts: Set[String] =
    productionsForSort
      .get(Sorts.Layout.head)
      .getOrElse(Set[Production]())
      .collect {
        case Production(_, _, _, Seq(RegexTerminal(_, terminalRegex, _)), _) => terminalRegex
        case p =>
          throw KEMException.compilerError(
            "Productions of sort `#Layout` must be exactly one `RegexTerminal`.",
            p
          )
      }

  lazy val layout: String = "(" + layouts.mkString(")|(") + ")"

  @transient
  lazy val definedKLabels: Set[KLabel] =
    productionsFor.keys.toSet.filter(!_.isInstanceOf[KVariable]).map(_.head)

  @transient
  lazy val localKLabels: Set[KLabel] =
    localProductionsFor.keys.toSet.filter(!_.isInstanceOf[KVariable])

  lazy val tokenSorts: Set[Sort] =
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
      Production(None, Seq(), s, Seq(), Att.empty.add(Att.TOKEN))

  lazy val allModuleNames: Set[String] = importedModuleNames + name

  def importedSentencesExcept(m: Module): Set[Sentence] =
    importedModules.flatMap { i =>
      if (m.allModuleNames contains i.name) Set.empty[Sentence] else i.localSentences
    }
  def sentencesExcept(m: Module): Set[Sentence] = importedSentencesExcept(m) | localSentences

  lazy val bracketProductionsFor: Map[Sort, List[Production]] =
    productions
      .collect { case p if p.att.contains(Att.BRACKET) => p }
      .groupBy(_.sort)
      .map { case (s, ps) => (s, ps.toList.sortBy(_.sort)(subsorts.asOrdering)) }

  @transient lazy val sortFor: Map[KLabel, Sort] = productionsFor.mapValues(_.head.sort)

  lazy val claims: Set[Claim]               = sentences.collect { case c: Claim => c }
  lazy val rules: Set[Rule]                 = sentences.collect { case r: Rule => r }
  lazy val rulesFor: Map[KLabel, Set[Rule]] = rules.groupBy(r => matchKLabel(r))
  lazy val macroKLabels: Set[KLabel]        = macroKLabelsFromRules ++ macroKLabelsFromProductions
  lazy val macroKLabelsFromRules: Set[KLabel] =
    rules.filter(r => r.isMacro).map(r => matchKLabel(r))
  lazy val macroKLabelsFromProductions: Set[KLabel] =
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

  lazy val contexts: Set[Context] = sentences.collect { case r: Context => r }

  lazy val sortedRules: Seq[Rule] = rules.toSeq.sorted

  lazy val localRules: Set[Rule]   = localSentences.collect { case r: Rule => r }
  lazy val localClaims: Set[Claim] = localSentences.collect { case r: Claim => r }

  // Check that productions with the same klabel have identical attributes
  //  productionsFor.foreach {
  //    case (l, ps) =>
  //      if (ps.groupBy(_.att).size != 1)
  //        throw DivergingAttributesForTheSameKLabel(ps)
  //  }

  @transient lazy val attributesFor: Map[KLabel, Att] = productionsFor.mapValues {
    mergeAttributes(_)
  }

  @transient lazy val signatureFor: Map[KLabel, Set[(Seq[Sort], Sort)]] =
    productionsFor.mapValues { ps: Set[Production] =>
      ps.filter { p: Production => p.params.isEmpty }
        .map { p: Production =>
          val params: Seq[Sort] = p.items.collect { case NonTerminal(sort, _) => sort }
          (params, p.sort)
        }
    }

  lazy val sortDeclarations: Set[SyntaxSort]      = sentences.collect { case s: SyntaxSort => s }
  lazy val sortSynonyms: Set[SortSynonym]         = sentences.collect { case s: SortSynonym => s }
  lazy val lexicalIdentifiers: Set[SyntaxLexical] = sentences.collect { case s: SyntaxLexical => s }

  lazy val sortSynonymMap: Map[Sort, Sort] = sortSynonyms.map(s => (s.newSort, s.oldSort)).toMap

  lazy val sortDeclarationsFor: Map[SortHead, Set[SyntaxSort]] =
    (sortDeclarations ++ allSorts.map(s => SyntaxSort(Seq(), s, Att.empty)))
      .groupBy(_.sort.head)

  @transient lazy val sortAttributesFor: Map[SortHead, Att] = sortDeclarationsFor.mapValues {
    mergeAttributes(_)
  }

  private def mergeAttributes[T <: Sentence](p: Set[T]) =
    Att.mergeAttributes(p.map(_.att))

  lazy val definedSorts: Set[SortHead] = (productions
    .filter(p => !p.isSortVariable(p.sort))
    .map(_.sort.head)) ++ (sortDeclarations.filter(s => s.params.isEmpty).map {
    _.sort.head
  }) ++ definedInstantiations.values.flatten.flatMap(_.params).filter(_.isNat).map(_.head)
  lazy val definedInstantiations: Map[SortHead, Set[Sort]] = {
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
      .map(_.sort.head))).map(s => s -> nonempty.getOrElse(s, Set())).toMap
  }
  lazy val allSorts: Set[Sort] = (definedSorts -- definedInstantiations.keys).map(
    Sort(_)
  ) ++ definedInstantiations.values.flatten
  lazy val localSorts: Set[Sort]             = allSorts -- fullImports.flatMap(_.allSorts)
  lazy val sortedDefinedSorts: Seq[SortHead] = definedSorts.toSeq.sorted
  lazy val sortedAllSorts: Seq[Sort]         = allSorts.toSeq.sorted

  lazy val listSorts: Set[Sort] = sentences.collect {
    case Production(_, _, srt, _, att1) if att1.contains(Att.USER_LIST) =>
      srt
  }

  lazy val subsorts: POSet[Sort]          = computeSubsortPOSet(sentences, false)
  lazy val syntacticSubsorts: POSet[Sort] = computeSubsortPOSet(sentences, true)
  lazy val overloads: POSet[Production]   = computeOverloadPOSet(subsorts, productions)

  private lazy val expressedPriorities: Set[(Tag, Tag)] =
    sentences
      .collect { case SyntaxPriority(ps, _) => ps }
      .map { ps: Seq[Set[Tag]] =>
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
      .flatten
  lazy val priorities = POSet(expressedPriorities)
  lazy val leftAssoc  = buildAssoc(Associativity.Left)
  lazy val rightAssoc = buildAssoc(Associativity.Right)

  private def buildAssoc(side: Associativity): Set[(Tag, Tag)] =
    sentences
      .collect { case SyntaxAssociativity(`side` | Associativity.NonAssoc, ps, _) => ps }
      .map { ps: Set[Tag] =>
        for {
          a <- ps
          b <- ps
        } yield (a, b)
      }
      .flatten

  @transient lazy val freshFunctionFor: Map[Sort, KLabel] =
    productions
      .groupBy(_.sort)
      .mapValues(_.filter(_.att.contains(Att.FRESH_GENERATOR)))
      .filter(_._2.nonEmpty)
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
      val res = items.collect {
        case nt: NonTerminal
            if !p.isSortVariable(nt.sort) && !definedSorts.contains(nt.sort.head) && !sortSynonymMap
              .contains(nt.sort) =>
          nt.sort
        case nt: NonTerminal
            if nt.sort.params.nonEmpty && (nt.sort.params.toSet & params.toSet).isEmpty && !definedInstantiations
              .getOrElse(nt.sort.head, Set())
              .contains(nt.sort) =>
          nt.sort
      }
      if (res.nonEmpty)
        throw KEMException.compilerError("Could not find sorts: " + res.asJava, p)
    case _ =>
  }

  def checkUserLists(): Unit = localSentences.foreach {
    case p @ Production(_, _, srt, _, atts) =>
      if (atts.contains(Att.USER_LIST)) {
        val prev = importedSentences.find(s =>
          s.isInstanceOf[Production]
            && s.asInstanceOf[Production].sort.equals(srt)
            && s.att.contains(Att.USER_LIST)
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
    (name, Set(flattened) ++ fullImports.map(m => m.flatModules._2).flatten)
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
  implicit val ord = new Ordering[Sentence] {
    def compare(a: Sentence, b: Sentence): Int =
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

case class SyntaxPriority(priorities: Seq[Set[Tag]], att: Att = Att.empty)
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
    Ordering.by[SyntaxPriority, (Seq[Seq[Tag]], Att)](s =>
      (s.priorities.map(_.toSeq.sorted), s.att)
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
    Ordering.by[SyntaxAssociativity, (Associativity, Seq[Tag], Att)](s =>
      (s.assoc, s.tags.toSeq.sorted, s.att)
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
//  def items: Seq[ProductionItem]
//  def klabel: Option[KLabel] =
//    att.get(Production.kLabelAttribute).headOption map { case KList(KToken(s, _, _)) => s } map { KLabel(_) }
//}

case class SyntaxSort(params: Seq[Sort], sort: Sort, att: Att = Att.empty)
    extends Sentence
    with SyntaxSortToString
    with OuterKORE {
  def items = Seq()

  override val isSyntax          = true
  override val isNonSyntax       = false
  override def withAtt(att: Att) = SyntaxSort(params, sort, att)
}
object SyntaxSort {
  implicit val ord: Ordering[SyntaxSort] = {
    import scala.math.Ordering.Implicits._
    Ordering.by[SyntaxSort, (Seq[String], String, Att)](s =>
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

case class SyntaxLexical(name: String, regex: String, att: Att = Att.empty)
    extends Sentence
    with SyntaxLexicalToString
    with OuterKORE {

  override val isSyntax          = true
  override val isNonSyntax       = false
  override def withAtt(att: Att) = SyntaxLexical(name, regex, att)
}
object SyntaxLexical {
  implicit val ord: Ordering[SyntaxLexical] =
    Ordering.by[SyntaxLexical, (String, String, Att)](s => (s.name, s.regex, s.att))
}

case class Production(
    klabel: Option[KLabel],
    params: Seq[Sort],
    sort: Sort,
    items: Seq[ProductionItem],
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

  def substitute(args: Seq[Sort]): Production = {
    val subst = params.zip(args).toMap
    Production(
      klabel.map(l => ADT.KLabel(l.name, args: _*)),
      Seq(),
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
  def recordProductions(uid: UidProvider): Set[Production] = {
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
      Set(Production(klabel, params, sort, prefix :+ suffix, newAtt.add(Att.RECORD_PRD_ZERO)))
    else if (namedNts.size == 1) {
      val main = Production(klabel, params, sort, prefix :+ suffix, newAtt.add(Att.RECORD_PRD_ZERO))
      val one = Production(
        klabel,
        params,
        sort,
        prefix :+ Terminal(namedNts.head.name.get) :+ Terminal(":") :+ namedNts.head :+ suffix,
        newAtt.add(Att.RECORD_PRD_ONE, namedNts.head.name.get)
      )
      Set(main, one)
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
        Seq(),
        Sort(baseName),
        Seq(Terminal("")),
        newAtt.add(Att.RECORD_PRD_EMPTY)
      )
      val subsort = Production(
        None,
        Seq(),
        Sort(baseName),
        Seq(NonTerminal(Sort(baseName + "Ne"), None)),
        newAtt.add(Att.RECORD_PRD_SUBSORT)
      )
      val repeat = Production(
        klabel,
        Seq(),
        Sort(baseName + "Ne"),
        Seq(
          NonTerminal(Sort(baseName + "Ne"), None),
          Terminal(","),
          NonTerminal(Sort(baseName + "Item"), None)
        ),
        newAtt.add(Att.RECORD_PRD_REPEAT)
      )
      val subsort2 = Production(
        None,
        Seq(),
        Sort(baseName + "Ne"),
        Seq(NonTerminal(Sort(baseName + "Item"), None)),
        newAtt.add(Att.RECORD_PRD_SUBSORT)
      )
      val namedItems: Set[Production] = namedNts
        .map(nt =>
          Production(
            klabel,
            Seq(),
            Sort(baseName + "Item"),
            Seq(Terminal(nt.name.get), Terminal(":"), NonTerminal(nt.sort, None)),
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
}

object Production {
  implicit val ord: Ordering[Production] =
    Ordering.by[Production, (Option[String], Att)](s => (s.klabel.map(_.name), s.att))

  def apply(
      klabel: KLabel,
      params: Seq[Sort],
      sort: Sort,
      items: Seq[ProductionItem],
      att: Att = Att.empty
  ): Production =
    Production(Some(klabel), params, sort, items, att)
  def apply(params: Seq[Sort], sort: Sort, items: Seq[ProductionItem], att: Att): Production =
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

case class RegexTerminal(precedeRegex: String, regex: String, followRegex: String)
    extends TerminalLike
    with RegexTerminalToString {
  lazy val pattern = new RunAutomaton(new RegExp(regex).toAutomaton, false)

  def compareTo(t: TerminalLike): Int = {
    if (t.isInstanceOf[Terminal]) {
      return 1;
    }
    return regex.compareTo(t.asInstanceOf[RegexTerminal].regex)
  }
}

case class Terminal(value: String)
    extends TerminalLike // hooked
    with TerminalToString {

  def compareTo(t: TerminalLike): Int = {
    if (t.isInstanceOf[RegexTerminal]) {
      return -1;
    }
    return value.compareTo(t.asInstanceOf[Terminal].value)
  }
}
