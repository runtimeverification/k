// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.outer

import collection.JavaConverters._
import org.kframework.kore._
import java.util.stream.StreamSupport

/**
 *
 * Helper constructors for KORE outer classes. The class is meant to be imported
 * statically.
 *
 */

object Constructors {
  import org.kframework.kore

  def Definition(requires: Set[Require], modules: Set[Module]) =
    kore.outer.Definition(requires, modules)

  def Require(file: java.io.File) = kore.outer.Require(file)
  def Module(name: String, sentences: Set[Sentence], att: Attributes) =
    kore.outer.Module(name, sentences, att)

  def SyntaxSort(sort: Sort) = outer.SyntaxSort(sort)
  def SyntaxSort(sort: Sort, att: Attributes) = outer.SyntaxSort(sort, att)

  def SyntaxProduction(sort: Sort, items: Seq[ProductionItem]) = outer.SyntaxProduction(sort, items)
  def SyntaxProduction(sort: Sort, items: Seq[ProductionItem], att: Attributes) = outer.SyntaxProduction(sort, items, att)

  def Terminal(s: String) = outer.Terminal(s)
  def NonTerminal(sort: Sort) = outer.NonTerminal(sort)
  def RegexTerminal(regexString: String) = outer.RegexTerminal(regexString)

  def Tag(s: String) = outer.Tag(s)

  def SyntaxPriority(priorities: Seq[Set[Tag]]) = outer.SyntaxPriority(priorities)
  def SyntaxPriority(priorities: Seq[Set[Tag]], att: Attributes) = outer.SyntaxPriority(priorities, att)

  def SyntaxAssociativity(assoc: outer.Associativity.Value, tags: Set[Tag]) = outer.SyntaxAssociativity(assoc, tags)
  def SyntaxAssociativity(assoc: outer.Associativity.Value, tags: Set[Tag], att: Attributes) = outer.SyntaxAssociativity(assoc, tags, att)

  def Context(content: K, requires: K) = outer.Context(content, requires)
  def Context(content: K, requires: K, att: Attributes) = outer.Context(content, requires, att)

  def Rule(body: K, requires: K, ensures: K, att: Attributes) = outer.Rule(body, requires, ensures, att)
  def Rule(body: K, requires: K, ensures: K) = outer.Rule(body, requires, ensures, Attributes())

  def Bubble(sentenceType: String, content: String, att: Attributes) =
    outer.Bubble(sentenceType, content, att)

  def Associativity = outer.Associativity;

  // EXTRA

  def Configuration(body: K, ensures: K, att: Attributes) = outer.Configuration(body, ensures, att)
}
