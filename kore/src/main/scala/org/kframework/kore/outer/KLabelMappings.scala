package org.kframework.kore.outer

import org.kframework.kore

trait KLabelMappings {
  self: Module =>

  lazy val labelsToProductions: Map[kore.KLabel, Set[SyntaxProduction]] =
    sentences collect {
      case prod: SyntaxProduction => (makeKLabel(prod.items), prod)
    } groupBy (_._1) mapValues (_ map { _._2 })

  def makeKLabel(items: Seq[ProductionItem]): kore.KLabel = kore.KLabel(
    items map {
      case NonTerminal(sort) => "_"
      case Terminal(string) => string
      case RegexTerminal(regex) => ???
    } mkString)
}