package org.kframework.compile

import org.kframework.compile.ConfigurationInfo.Multiplicity
import org.kframework.definition.{Module, NonTerminal, Production}
import org.kframework.kore.{KLabel, Sort}

class ConfigurationInfoFromModule(m: Module) extends ConfigurationInfo {

  println("\n>>>>>>\n")
  private val cellProductions: Set[Production] = m.productions.filter(_.att.contains("cell"))
  private val cellSorts: Map[Sort, Production] = cellProductions.map(p => (p.sort, p)).toMap
  private val cellKLabels: Set[KLabel] = cellProductions map {_.klabel.get}

  private val edges: Set[(KLabel, KLabel)] = cellProductions flatMap { p =>
    p.items collect { case NonTerminal(s) if cellSorts.contains(s) => (p, cellSorts(s)) }
  } map { case (a, b) => (a.klabel.get, b.klabel.get) }

  private val topCells = cellKLabels filter { case l: KLabel => !(edges exists { case (_, `l`) => true;
  case _ =>
    false
  })
  }

  println(edges)

  if (topCells.size > 1)
    throw new AssertionError("Too many top cells:" + topCells)

  val topCell = topCells.head
  val levels: Map[KLabel, Int] = edges.foldLeft(Map(topCell -> 0)) {
    case (m: Map[KLabel, Int], (from: KLabel, to: KLabel)) =>
      m + (to -> (m(from) + 1))
  }


  println("\n<<<<<<\n")

  override def getLevel(k: KLabel): Int = levels(k)
  override def isParentCell(k: KLabel): Boolean = edges exists { case (c, _) => c == k }

  // todo: Cosmin: very, very approximate implementation -- will have to think about it
  override def getMultiplicity(k: KLabel): Multiplicity =
    if (m.productionsFor(k).exists(_.att.contains("assoc")))
      Multiplicity.STAR
    else
      Multiplicity.ONE

  override def getParent(k: KLabel): KLabel = edges collectFirst { case (p, `k`) => p } get
  override def isCell(k: KLabel): Boolean = cellKLabels.contains(k)
  override def isLeafCell(k: KLabel): Boolean = k != topCell
}
