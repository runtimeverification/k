// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.outer

import collection.JavaConverters._
import org.kframework.kore._;

/**
 *
 * Helper constructors for KORE outer classes. The class is meant to be imported
 * statically.
 *
 */

object Constructors {
  import outer._
  import org.kframework.kore

  def immutable[T](s: java.util.Set[T]): Set[T] = s.asScala.toSet
  def immutable[T](s: java.util.List[T]): Seq[T] = s.asScala
  def immutable[T](s: Array[T]): Seq[T] = s

  def KList(s: java.util.Set[K]): KList = kore.KList(s.asScala.toSeq: _*)
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

  def Tag(s: String) = outer.Tag(s)

  def SyntaxPriority(priorities: Seq[Set[Tag]]) = outer.SyntaxPriority(priorities)
  def SyntaxPriority(priorities: Seq[Set[Tag]], att: Attributes) = outer.SyntaxPriority(priorities, att)

  def SyntaxAssociativity(assoc: outer.Associativity.Value, tags: Set[Tag]) = outer.SyntaxAssociativity(assoc, tags)
  def SyntaxAssociativity(assoc: outer.Associativity.Value, tags: Set[Tag], att: Attributes) = outer.SyntaxAssociativity(assoc, tags, att)

  def Associativity = outer.Associativity;
}