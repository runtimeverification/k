// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.outer

import org.kframework.kore
import org.kframework.kore.Sort
import scala.util.matching.Regex
import org.kframework.kore.Attributes

trait OuterKORE

case class Definition(requires: Set[Require], modules: Set[Module])
  extends DefinitionToString with OuterKORE

case class Require(file: java.io.File) extends OuterKORE

case class Module(name: String, sentences: Set[Sentence], att: Attributes = Attributes())
  extends ModuleToString with KLabelMappings with OuterKORE
// hooked but different from core, Import is a sentence here

trait Sentence { // marker
  val att: Attributes
}

case class Context(
  body: kore.K,
  requires: kore.K,
  att: Attributes = Attributes()) extends Sentence with OuterKORE with ContextToString

case class Rule(
  body: kore.K,
  requires: kore.K,
  ensures: kore.K,
  att: Attributes) extends Sentence
  with RuleToString with OuterKORE

case class ModuleComment(comment: String, att: Attributes = Attributes())
  extends Sentence with OuterKORE

case class Import(what: String, att: Attributes = Attributes())
  extends Sentence with ImportToString with OuterKORE // hooked

// syntax declarations

case class SyntaxPriority(priorities: Seq[Set[Tag]], att: Attributes = Attributes())
  extends Sentence with SyntaxPriorityToString with OuterKORE

object Associativity extends Enumeration {
  type Value1 = Value
  val Left, Right, NonAssoc, Unspecified = Value
}

case class SyntaxAssociativity(assoc: Associativity.Value, tags: collection.immutable.Set[Tag], att: Attributes = Attributes())
  extends Sentence with SyntaxAssociativityToString with OuterKORE

case class Tag(name: String) extends TagToString with OuterKORE

case class SyntaxSort(sort: Sort, att: Attributes = Attributes()) extends Sentence
  with SyntaxSortToString with OuterKORE

case class SyntaxProduction(sort: Sort, items: Seq[ProductionItem], att: Attributes = Attributes())
  extends Sentence with SyntaxProductionToString // hooked but problematic, see kast-core.k

sealed trait ProductionItem extends OuterKORE // marker

case class NonTerminal(sort: Sort) extends ProductionItem
  with NonTerminalToString
case class RegexTerminal(regex: String) extends ProductionItem with RegexTerminalToString
case class Terminal(value: String) extends ProductionItem // hooked
  with TerminalToString

/* Helper constructors */
object NonTerminal {
  def apply(sort: String): NonTerminal = NonTerminal(Sort(sort))
}
