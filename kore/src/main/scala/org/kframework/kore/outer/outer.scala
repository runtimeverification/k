package org.kframework.kore.outer

import org.kframework.kore
import org.kframework.kore.Sort
import scala.util.matching.Regex
import org.kframework.kore.Attributes

case class Definition(requires: Set[Require], modules: Set[Module])
  extends DefinitionToString

case class Require(file: java.io.File)

case class Module(name: String, sentences: Set[Sentence], att: Attributes = Attributes())
  extends ModuleToString with KLabelMappings
// hooked but different from core, Import is a sentence here

trait Sentence { // marker
  val att: Attributes
}

case class Context(
  body: kore.K,
  requires: kore.K,
  att: Attributes = Attributes()) extends Sentence

case class Rule(
  body: kore.K,
  requires: kore.K,
  ensures: kore.K,
  att: Attributes) extends Sentence
  with RuleToString

case class ModuleComment(comment: String, att: Attributes = Attributes()) extends Sentence

case class Import(what: String, att: Attributes = Attributes()) extends Sentence with ImportToString // hooked

// syntax declarations

case class SyntaxPriority(priorities: Seq[Set[Tag]], att: Attributes = Attributes())
  extends Sentence with SyntaxPriorityToString

object Associativity extends Enumeration {
  type Value1 = Value
  val Left, Right, NonAssoc, Unspecified = Value
}

case class SyntaxAssociativity(assoc: Associativity.Value, tags: collection.immutable.Set[Tag], att: Attributes = Attributes())
  extends Sentence with SyntaxAssociativityToString

case class Tag(name: String) extends TagToString

case class SyntaxSort(sort: Sort, att: Attributes = Attributes()) extends Sentence
  with SyntaxSortToString

case class SyntaxProduction(sort: Sort, items: Seq[ProductionItem], att: Attributes = Attributes())
  extends Sentence with SyntaxProductionToString // hooked but problematic, see kast-core.k

sealed trait ProductionItem // marker

case class NonTerminal(sort: Sort) extends ProductionItem
  with NonTerminalToString
case class RegexTerminal(regex: String) extends ProductionItem
case class Terminal(value: String) extends ProductionItem // hooked
  with TerminalToString

/* Helper constructors */
object NonTerminal {
  def apply(sort: String): NonTerminal = NonTerminal(Sort(sort))
}

// ***** Extra *****

case class Configuration(
  body: kore.K,
  ensures: kore.K,
  att: Attributes = Attributes()) extends Sentence

case class Bubble(contents: String, att: Attributes = Attributes()) extends Sentence
