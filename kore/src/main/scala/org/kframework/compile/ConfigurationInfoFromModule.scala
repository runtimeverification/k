package org.kframework.compile

import org.kframework.compile.ConfigurationInfo.Multiplicity
import org.kframework.definition.{Production, NonTerminal, Module}
import org.kframework.kore.{Sort, KLabel}

class ConfigurationInfoFromModule(m: Module) extends ConfigurationInfo {

  println("\n>>>>>>\n")
  private val cellProductions: Set[Production] = m.productions.filter(_.att.contains("cell"))
  private val cellSorts: Map[Sort, Production] = cellProductions.map(p => (p.sort, p)).toMap
  private val cellKLabels: Set[KLabel] = cellProductions map {_.klabel.get}

  private val edges: Set[(KLabel, KLabel)] = cellProductions flatMap { p =>
    p.items collect { case NonTerminal(s) if cellSorts.contains(s) => (p, cellSorts(s)) }
  } map { case (a, b) => (a.klabel.get, b.klabel.get) }

  private val topCells = cellKLabels filter { case l: KLabel => !(edges exists { case (_, `l`) => true; case _ => false }) }

  println(edges)

  if (topCells.size > 1)
  throw new AssertionError("Too many top cells:" + topCells)



  println("\n<<<<<<\n")

  override def getLevel(k: KLabel): Int = ???
  override def isParentCell(k: KLabel): Boolean = ???
  override def getMultiplicity(k: KLabel): Multiplicity = ???
  override def getParent(k: KLabel): KLabel = ???
  override def isCell(k: KLabel): Boolean = ???
  override def isLeafCell(k: KLabel): Boolean = ???
}
