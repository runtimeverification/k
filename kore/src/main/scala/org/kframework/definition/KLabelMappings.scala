package org.kframework.definition

import org.kframework.koreimplementation

trait KLabelMappings {
  self: Module =>

  lazy val labelsToProductions: Map[koreimplementation.KLabel, Set[SyntaxProduction]] =
    sentences collect {
      case prod: SyntaxProduction => (makeKLabel(prod.items), prod)
    } groupBy (_._1) mapValues (_ map { _._2 })

  def makeKLabel(items: Seq[ProductionItem]): koreimplementation.KLabel = koreimplementation.KLabel(
    items map {
      case NonTerminal(sort) => "_"
      case Terminal(string) => string
      case RegexTerminal(regex) => ???
    } mkString)
}
