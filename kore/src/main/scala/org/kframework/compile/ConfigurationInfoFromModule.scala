package org.kframework.compile

import java.util

import org.kframework.kore.ADT.{KList, KApply}

import scala.collection.JavaConverters._

import org.kframework.compile.ConfigurationInfo.Multiplicity
import org.kframework.definition.{Module, NonTerminal, Production}
import org.kframework.kore.{K, KLabel, Sort}

object ConfigurationInfoFromModule

class ConfigurationInfoFromModule(val m: Module) extends ConfigurationInfo {

  private val cellProductions: Map[Sort,Production] =
    m.productions.filter(_.att.contains("cell")).map(p => (p.sort, p)).toMap
  private val cellSorts: Set[Sort] = cellProductions.keySet
  val cellLabels: Map[Sort, KLabel] = cellProductions.mapValues(_.klabel.get)
  private val cellInitializer: Map[Sort, K] =
    m.productions.filter(p => cellSorts(p.sort) && p.att.contains("initializer"))
      .map(p => (p.sort, KApply(p.klabel.get,KList(List.empty)))).toMap

  private val edges: Set[(Sort, Sort)] = cellProductions.flatMap { case (s,p) =>
    p.items.collect{ case NonTerminal(n) if cellSorts.contains(n) => (s, n)}}.toSet

  private val topCells = cellSorts.filter (l => !edges.map(_._2).contains(l))

  println(edges)

  if (topCells.size > 1)
    throw new AssertionError("Too many top cells:" + topCells)

  val topCell: Sort = topCells.head
  val levels: Map[Sort, Int] = edges.foldLeft(Map(topCell -> 0)) {
    case (m: Map[Sort, Int], (from: Sort, to: Sort)) =>
      m + (to -> (m(from) + 1))
  }

  override def getLevel(k: Sort): Int = levels(k)
  override def isParentCell(k: Sort): Boolean = edges exists { case (c, _) => c == k }

  // todo: Cosmin: very, very approximate implementation -- will have to think about it
  override def getMultiplicity(k: Sort): Multiplicity =
    if (m.productionsFor(cellLabels(k)).exists(_.att.contains("assoc")))
      Multiplicity.STAR
    else
      Multiplicity.ONE

  override def getParent(k: Sort): Sort = edges collectFirst { case (p, `k`) => p } get
  override def isCell(k: Sort): Boolean = cellSorts.contains(k)
  override def isLeafCell(k: Sort): Boolean = !isParentCell(k)

  override def getChildren(k: Sort): util.List[Sort] = edges.toList.collect { case (`k`,p) => p }.asJava

  override def leafCellType(k: Sort): Sort = cellProductions(k).items.collectFirst{ case NonTerminal(n) => n} get

  override def getDefaultCell(k: Sort): K = cellInitializer(k)

  override def getCellLabel(k: Sort): KLabel = cellLabels(k)
}
