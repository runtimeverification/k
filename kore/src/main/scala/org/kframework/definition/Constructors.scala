// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework.definition

import org.kframework.attributes
import org.kframework.attributes.Att
import org.kframework.definition
import org.kframework.kore._
import scala.collection.{ IndexedSeq => _, Seq => _, _ }

/**
 * Helper constructors for KORE definition.classes. The class is meant to be imported statically.
 */

object Constructors {

  def Definition(mainModule: Module, modules: Set[Module], att: Att) =
    definition.Definition(mainModule, modules, att)

  def Import(module: Module, isPublic: Boolean) =
    definition.Import(module, isPublic)

  def Module(name: String, imports: Set[Import], sentences: Set[Sentence], att: attributes.Att) =
    definition.Module(name, imports, sentences, att)

  def SyntaxSort(params: Seq[Sort], sort: Sort) = definition.SyntaxSort(params, sort)
  def SyntaxSort(params: Seq[Sort], sort: Sort, att: attributes.Att) =
    definition.SyntaxSort(params, sort, att)

  def SortSynonym(newSort: Sort, oldSort: Sort) = definition.SortSynonym(newSort, oldSort)
  def SortSynonym(newSort: Sort, oldSort: Sort, att: attributes.Att) =
    definition.SortSynonym(newSort, oldSort, att)

  def SyntaxLexical(name: String, regex: String) = definition.SyntaxLexical(name, regex)
  def SyntaxLexical(name: String, regex: String, att: attributes.Att) =
    definition.SyntaxLexical(name, regex, att)

  def Production(params: Seq[Sort], sort: Sort, items: Seq[ProductionItem]) =
    definition.Production(params, sort, items, Att.empty)
  def Production(params: Seq[Sort], sort: Sort, items: Seq[ProductionItem], att: attributes.Att) =
    definition.Production(params, sort, items, att)
  def Production(klabel: KLabel, sort: Sort, items: Seq[ProductionItem]) =
    definition.Production(klabel, klabel.params, sort, items)
  def Production(klabel: KLabel, sort: Sort, items: Seq[ProductionItem], att: attributes.Att) =
    definition.Production(klabel, klabel.params, sort, items, att)
  def Production(
      klabel: Option[KLabel],
      params: Seq[Sort],
      sort: Sort,
      items: Seq[ProductionItem]
  ) = definition.Production(klabel, params, sort, items, Att.empty)
  def Production(
      klabel: Option[KLabel],
      params: Seq[Sort],
      sort: Sort,
      items: Seq[ProductionItem],
      att: attributes.Att
  ) = definition.Production(klabel, params, sort, items, att)

  def Terminal(s: String)                           = definition.Terminal(s)
  def NonTerminal(sort: Sort)                       = definition.NonTerminal(sort, None)
  def NonTerminal(sort: Sort, name: Option[String]) = definition.NonTerminal(sort, name)
  def RegexTerminal(regexString: String) = definition.RegexTerminal("#", regexString, "#")
  def RegexTerminal(precedeRegexString: String, regexString: String, followRegexString: String) =
    definition.RegexTerminal(precedeRegexString, regexString, followRegexString)

  def Tag(s: String) = definition.Tag(s)

  def SyntaxPriority(priorities: Seq[Set[Tag]]) = definition.SyntaxPriority(priorities)
  def SyntaxPriority(priorities: Seq[Set[Tag]], att: attributes.Att) =
    definition.SyntaxPriority(priorities, att)

  def SyntaxAssociativity(assoc: definition.Associativity, tags: Set[Tag]) =
    definition.SyntaxAssociativity(assoc, tags)
  def SyntaxAssociativity(assoc: definition.Associativity, tags: Set[Tag], att: attributes.Att) =
    definition.SyntaxAssociativity(assoc, tags, att)

  def Context(content: K, requires: K) = definition.Context(content, requires)
  def Context(content: K, requires: K, att: attributes.Att) =
    definition.Context(content, requires, att)

  def ContextAlias(content: K, requires: K) = definition.ContextAlias(content, requires)
  def ContextAlias(content: K, requires: K, att: attributes.Att) =
    definition.ContextAlias(content, requires, att)

  def Claim(body: K, requires: K, ensures: K, att: attributes.Att) =
    definition.Claim(body, requires, ensures, att)
  def Claim(body: K, requires: K, ensures: K) = definition.Claim(body, requires, ensures, Att.empty)

  def Rule(body: K, requires: K, ensures: K, att: attributes.Att) =
    definition.Rule(body, requires, ensures, att)
  def Rule(body: K, requires: K, ensures: K) = definition.Rule(body, requires, ensures, Att.empty)

  def Bubble(sentenceType: String, content: String, att: attributes.Att) =
    definition.Bubble(sentenceType, content, att)

  // EXTRA

  def Configuration(body: K, ensures: K, att: attributes.Att) =
    definition.Configuration(body, ensures, att)
}
