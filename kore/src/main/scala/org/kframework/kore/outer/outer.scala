package org.kframework.kore.outer

import org.kframework.kore
import org.kframework.kore.Sort
import scala.util.matching.Regex
import org.kframework.kore.Attributes

trait ParserPiece

case class Definition(requires: Set[Require], modules: Set[Module])
  extends DefinitionToString with ParserPiece

case class Require(file: java.io.File)

object Module {
  def apply(name: String, att: Attributes, sentences: Set[Sentence]): Module =
    Module(name, sentences, att)
}

case class Module(name: String, sentences: Set[Sentence], att: Attributes = Attributes())
  extends ModuleToString with ParserPiece with KLabelMappings
// hooked but different from core, Import is a sentence here

trait Sentence { // marker
  val attributes: Attributes
}

case class Rule(
  label: String,
  body: kore.K,
  requires: kore.K,
  ensures: kore.K,
  attributes: Attributes) extends Sentence
  with RuleToString

case class Configuration(contents: kore.K, attributes: Attributes = Attributes()) extends Sentence // hooked
  with ConfigurationToString

case class ModuleComment(comment: String, attributes: Attributes = Attributes()) extends Sentence

case class Import(what: String, attributes: Attributes = Attributes()) extends Sentence // hooked

case class SyntaxPriority(higher: String, lower: String, attributes: Attributes = Attributes()) extends Sentence with ParserPiece

// will be needed once we figure out how to encode associtivity
//object Associativity extends Enumeration {
//  val Left, Right, NonAssoc, Unspecified = Value
//}

case class SyntaxSort(sort: Sort, attributes: Attributes = Attributes()) extends Sentence with ParserPiece

case class SyntaxProduction(sort: Sort, items: Seq[ProductionItem], attributes: Attributes = Attributes()) extends Sentence with ParserPiece // hooked but problematic, see kast-core.k 
  with SyntaxProductionToString

sealed trait ProductionItem // marker

case class NonTerminal(sort: Sort) extends ProductionItem 
case class RegexTerminal(regex: String) extends ProductionItem 
case class Terminal(value: String) extends ProductionItem // hooked
  with TerminalToString

/* Helper constructors */
object NonTerminal {
  def apply(sort: String): NonTerminal = NonTerminal(Sort(sort))
}
