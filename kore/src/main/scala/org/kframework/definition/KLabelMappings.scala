package org.kframework.definition

import org.kframework.kore
import org.kframework.kore.ADT

trait KLabelMappings {
  self: Module =>

  lazy val labelsToProductions: Map[kore.KLabel, Set[Production]] =
    sentences collect {
      case prod: Production => (makeKLabel(prod.items), prod)
    } groupBy (_._1) mapValues (_ map { _._2 })

  def makeKLabel(items: Seq[ProductionItem]): kore.KLabel = ADT.KLabel(
    items map {
      case NonTerminal(sort) => "_"
      case Terminal(string, _) => string
      //TODO(cos): remove this
      case RegexTerminal(regex, _) => "regexp"
    } mkString)
}
