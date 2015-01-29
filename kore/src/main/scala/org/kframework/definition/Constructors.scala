// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.definition

import org.kframework.definition
import org.kframework.koreimplementation._

/**
 *
 * Helper constructors for KORE definition.classes. The class is meant to be imported
 * statically.
 *
 */

object Constructors {

  def Definition(requires: Set[Require], modules: Set[Module]) =
    definition.Definition(requires, modules)

  def Require(file: java.io.File) = definition.Require(file)
  def Module(name: String, imports: Set[Module], sentences: Set[Sentence], att: Attributes) =
    definition.Module(name, imports, sentences, att)

  def SyntaxSort(sort: Sort) = definition.SyntaxSort(sort)
  def SyntaxSort(sort: Sort, att: Attributes) = definition.SyntaxSort(sort, att)

  def SyntaxProduction(sort: Sort, items: Seq[ProductionItem]) = definition.SyntaxProduction(sort, items)
  def SyntaxProduction(sort: Sort, items: Seq[ProductionItem], att: Attributes) = definition.SyntaxProduction(sort, items, att)

  def Terminal(s: String) = definition.Terminal(s)
  def NonTerminal(sort: Sort) = definition.NonTerminal(sort)
  def RegexTerminal(regexString: String) = definition.RegexTerminal(regexString)

  def Tag(s: String) = definition.Tag(s)

  def SyntaxPriority(priorities: Seq[Set[Tag]]) = definition.SyntaxPriority(priorities)
  def SyntaxPriority(priorities: Seq[Set[Tag]], att: Attributes) = definition.SyntaxPriority(priorities, att)

  def SyntaxAssociativity(assoc: definition.Associativity.Value, tags: Set[Tag]) = definition.SyntaxAssociativity(assoc, tags)
  def SyntaxAssociativity(assoc: definition.Associativity.Value, tags: Set[Tag], att: Attributes) = definition.SyntaxAssociativity(assoc, tags, att)

  def Context(content: K, requires: K) = definition.Context(content, requires)
  def Context(content: K, requires: K, att: Attributes) = definition.Context(content, requires, att)

  def Rule(body: K, requires: K, ensures: K, att: Attributes) = definition.Rule(body, requires, ensures, att)
  def Rule(body: K, requires: K, ensures: K) = definition.Rule(body, requires, ensures, Attributes())

  def Bubble(sentenceType: String, content: String, att: Attributes) =
    definition.Bubble(sentenceType, content, att)

  def Associativity = definition.Associativity;

  // EXTRA

  def Configuration(body: K, ensures: K, att: Attributes) = definition.Configuration(body, ensures, att)
}
