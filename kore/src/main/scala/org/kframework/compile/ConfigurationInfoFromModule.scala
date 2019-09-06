package org.kframework.compile

import java.util

import org.kframework.POSet
import org.kframework.kore.KORE.{KApply, KLabel}

import scala.collection.JavaConverters._
import org.kframework.compile.ConfigurationInfo.Multiplicity
import org.kframework.definition.{Module, NonTerminal, Production, Rule}
import org.kframework.kore._
import org.kframework.TopologicalSort._
import org.kframework.utils.errorsystem.KEMException

import org.kframework.builtin.Sorts

import collection._

object ConfigurationInfoFromModule

class ConfigurationInfoFromModule(val m: Module) extends ConfigurationInfo {

  private val cellProductionsSet:    Set[(Sort, Production)] = m.productions.filter(_.att.contains("cell"))          .map(p => (p.sort, p))
  private val cellBagProductionsSet: Set[(Sort, Production)] = m.productions.filter(_.att.contains("cellCollection")).map(p => (p.sort, p))

  private val cellSorts:    Set[Sort] = cellProductionsSet   .map({sp => sp._1})
  private val cellBagSorts: Set[Sort] = cellBagProductionsSet.map({sp => sp._1})

  private def buildCellProductionMap(cells: Set[(Sort, Production)]): Map[Sort, Production] = {
    def buildCellProductionMap(_cells: Set[(Sort, Production)], _cellMap: Map[Sort, Production]): Map[Sort, Production] = {
      if (_cells.size == 0)
        return _cellMap
      val (s, p) = _cells.head
      if (_cellMap.contains(s))
        throw KEMException.compilerError("Too many productions for cell sort: " + s)
      buildCellProductionMap(_cells.tail, _cellMap + (s -> p))
    }
    buildCellProductionMap(cells, Map())
  }

  private val cellProductions:    Map[Sort,Production] = buildCellProductionMap(cellProductionsSet)
  private val cellBagProductions: Map[Sort,Production] = buildCellProductionMap(cellBagProductionsSet)

  private val cellBagSubsorts: Map[Sort, Set[Sort]] = cellBagProductions.values.map(p => (p.sort, getCellSortsOfCellBag(p.sort))).toMap
  private val cellLabels: Map[Sort, KLabel] = cellProductions.mapValues(_.klabel.get)
  private val cellLabelsToSorts: Map[KLabel, Sort] = cellLabels.map(_.swap)

  private val cellFragmentLabel: Map[Sort,KLabel] =
    m.productions.filter(_.att.contains("cellFragment", classOf[Sort]))
      .map(p => (p.att.get("cellFragment", classOf[Sort]),p.klabel.get)).toMap
  private val cellAbsentLabel: Map[Sort,KLabel] =
    m.productions.filter(_.att.contains("cellOptAbsent", classOf[Sort]))
      .map (p => (p.att.get("cellOptAbsent", classOf[Sort]),p.klabel.get)).toMap


  private val cellInitializer: Map[Sort, KApply] =
    m.productions.filter(p => (cellSorts(p.sort) || cellBagSorts(p.sort)) && p.att.contains("initializer"))
      .map(p => (p.sort, KApply(p.klabel.get))).flatMap({ case (s, app) => if (cellBagSorts(s)) getCellSortsOfCellBag(s).map((_, app)) else Seq((s, app))}).toMap

  private val edges: Set[(Sort, Sort)] = cellProductions.toList.flatMap { case (s,p) =>
    p.items.flatMap{
      case NonTerminal(n, _) if cellSorts.contains(n) => List((s, n))
      case NonTerminal(n, _) if cellBagSorts.contains(n) => getCellSortsOfCellBag(n).map(subsort => (s, subsort))
      case _ => List()
    }}.toSet

  private def getCellSortsOfCellBag(n: Sort): Set[Sort] = {
    m.definedSorts.filter(m.subsorts.directlyGreaterThan(n, _))
  }

  override def getCellBagSortsOfCell(n: Sort): Set[Sort] = {
    m.definedSorts.filter(m.subsorts.directlyLessThan(n, _)).intersect(cellBagSorts)
  }

  private val edgesPoset: POSet[Sort] = POSet(edges)

  private lazy val topCells = cellSorts.diff(edges.map(_._2))

  private val sortedSorts: Seq[Sort]         = tsort(edges).toSeq
  private val sortedEdges: Seq[(Sort, Sort)] = edges.toList.sortWith((l, r) => sortedSorts.indexOf(l._1) < sortedSorts.indexOf(r._1))
  val levels: Map[Sort, Int] = sortedEdges.foldLeft(topCells.map((_, 0)).toMap) {
    case (m: Map[Sort, Int], (from: Sort, to: Sort)) =>
      m + (to -> (m(from) + 1))
  }

  private lazy val mainCell = {
    val mainCells = cellProductions.filter(x => x._2.att.contains("maincell")).map(_._1)
    if (mainCells.size > 1)
      throw KEMException.compilerError("Too many main cells:" + mainCells)
    if (mainCells.isEmpty)
      throw KEMException.compilerError("No main cell found")
    mainCells.head
  }

  override def getLevel(k: Sort): Int = levels.getOrElse(k, -1)
  override def isParentCell(k: Sort): Boolean = edges exists { case (c, _) => c == k }

  override def getMultiplicity(k: Sort): Multiplicity =
    if (cellBagSubsorts.values.flatten.toSet.contains(k))
      Multiplicity.STAR
    else if (cellProductions(k).att.contains("unit"))
      Multiplicity.OPTIONAL
    else
      Multiplicity.ONE

  override def getParent(k: Sort): Sort = edges collectFirst { case (p, `k`) => p } get
  override def isCell(k: Sort): Boolean = cellSorts.contains(k)
  override def isCellCollection(s: Sort): Boolean = cellBagSorts.contains(s)
  override def isCellLabel(kLabel: KLabel): Boolean = cellLabelsToSorts.contains(kLabel)
  override def isLeafCell(k: Sort): Boolean = !isParentCell(k)

  override def getChildren(k: Sort): util.List[Sort] = cellProductions(k).items.filter(_.isInstanceOf[NonTerminal]).map(_.asInstanceOf[NonTerminal].sort).flatMap {s => {
    if (cellBagSorts(s))
      getCellSortsOfCellBag(s).toSeq
    else
      Seq(s)
  }}.asJava

  override def leafCellType(k: Sort): Sort = cellProductions(k).items.collectFirst{ case NonTerminal(n, _) => n} get

  override def getDefaultCell(k: Sort): KApply = cellInitializer(k)

  override def isConstantInitializer(k: Sort): Boolean = {
    !m.productionsFor(getDefaultCell(k).klabel).exists(_.items.exists(_.isInstanceOf[NonTerminal]))
  }

  override def getCellLabel(k: Sort): KLabel = cellLabels(k)
  override def getCellSort(kLabel: KLabel): Sort = cellLabelsToSorts(kLabel)

  override def getCellFragmentLabel(k : Sort): KLabel = cellFragmentLabel(k)
  override def getCellAbsentLabel(k: Sort): KLabel = cellAbsentLabel(k)

  override def getRootCell: Sort = {
    if (topCells.size > 1)
      throw KEMException.compilerError("Too many top cells for module " + m.name + ": " + topCells)
    topCells.head
  }

  override def getComputationCell: Sort = mainCell
  override def getCellSorts: util.Set[Sort] = cellSorts.asJava

  override def getUnit(k: Sort): KApply = {
    if (getMultiplicity(k) == Multiplicity.OPTIONAL)
      KApply(KLabel(cellProductions(k).att.get("unit")))
    else {
      val sorts = getCellBagSortsOfCell(k)
      assert(sorts.size == 1, "Too many cell bags found for cell sort: " + k + ", " + sorts)
      KApply(KLabel(cellBagProductions(sorts.head).att.get("unit")))
    }
  }

  override def getConcat(k: Sort): KLabel = {
    val sorts = getCellBagSortsOfCell(k)
    assert(sorts.size == 1, "Too many cell bags found for cell sort: " + k + ", " + sorts)
    cellBagProductions(sorts.head).klabel.get
  }

  override def getCellForConcat(concat: KLabel): Option[Sort] = cellSorts
    .map(s => (s, getCellBagSortsOfCell(s)))
    .filter(_._2.size == 1)
    .filter(p => cellBagProductions(p._2.head).klabel.get.equals(concat) || (cellInitializer.contains(p._1) && cellInitializer(p._1).klabel == concat))
    .map(_._1)
    .headOption

  override def getCellForUnit(unitLabel: KLabel): Option[Sort] = {
    val unit = KApply(unitLabel)
    cellSorts
      .map(s => (s, getCellBagSortsOfCell(s)))
      .filter(_._2.size == 1)
      .filter(p => KApply(KLabel(cellBagProductions(p._2.head).att.get("unit"))).equals(unit))
      .map(_._1)
      .headOption
  }


  lazy val initRules: Set[Rule] = m.rules.collect({ case r if r.att.contains("initializer") => r })

  lazy val configVars: Set[KToken] = {
    val transformer = new FoldK[Set[KToken]] {
      override def apply(k: KToken): Set[KToken] = {
        if (k.sort == Sorts.KConfigVar) Set(k) else unit
      }
      def unit = Set()
      def merge(set1: Set[KToken], set2: Set[KToken]) = set1 | set2
    }
    initRules.map(r => transformer.apply(r.body))
      .fold(transformer.unit)(transformer.merge)
  }

  lazy val cellProductionsFor: Map[Sort, Set[Production]] =
    m.productions
      .collect({ case p if p.att.contains("cell") => p })
      .groupBy(_.sort)
      .map { case (s, ps) => (s, ps) }

}
