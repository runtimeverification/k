package org.kframework.kore.outer

import org.kframework.kore
import org.kframework.kore.Sort
import scala.util.matching.Regex
import org.kframework.kore.Attributes

trait ParserPiece

case class Definition(requires: Set[Require], modules: Set[Module])
  extends DefinitionToString with ParserPiece

case class Require(file: java.io.File)

case class Module(name: String, sentences: Set[Sentence], att: Attributes = Attributes())
  extends ModuleToString with ParserPiece with KLabelMappings
// hooked but different from core, Import is a sentence here

trait Sentence { // marker
  val att: Attributes
}

case class Rule(
  label: String,
  body: kore.K,
  requires: kore.K,
  ensures: kore.K,
  att: Attributes) extends Sentence
  with RuleToString

case class ModuleComment(comment: String, att: Attributes = Attributes()) extends Sentence

case class Import(what: String, att: Attributes = Attributes()) extends Sentence // hooked

case class SyntaxPriority(higher: String, lower: String, att: Attributes = Attributes()) extends Sentence with ParserPiece

// will be needed once we figure out how to encode associativity
//object Associativity extends Enumeration {
//  val Left, Right, NonAssoc, Unspecified = Value
//}

case class SyntaxSort(sort: Sort, att: Attributes = Attributes()) extends Sentence
  with ParserPiece with SyntaxSortToString

case class SyntaxProduction(sort: Sort, items: Seq[ProductionItem], att: Attributes = Attributes()) extends Sentence with ParserPiece // hooked but problematic, see kast-core.k 
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
