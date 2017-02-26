package org.kframework.minikore


import org.kframework.minikore.{PatternInterface => i}

import scala.collection._

/** Algebraic data type of MiniKore. */
object MiniKore {

  //Default Implementation

  type Attributes = Seq[i.Pattern]

  case class Definition(modules: Seq[Module], att: Attributes)

  case class Module(name: String, sentences: Seq[Sentence], att: Attributes)

  sealed trait Sentence

  case class Import(name: String, att: Attributes) extends Sentence

  case class SortDeclaration(sort: String, att: Attributes) extends Sentence

  case class SymbolDeclaration(sort: String, label: String, args: Seq[String], att: Attributes) extends Sentence

  case class Rule(pattern: i.Pattern, att: Attributes) extends Sentence

  case class Axiom(pattern: i.Pattern, att: Attributes) extends Sentence

  case class Variable(_1: i.Name, _2: i.Sort) extends i.Variable

  case class DomainValue(_1: i.Label, _2: i.Value) extends i.DomainValue

  case class Application(_1: i.Label, args: Seq[i.Pattern]) extends i.Application

  case class Top() extends i.Top

  case class Bottom() extends i.Bottom

  case class And(_1: i.Pattern, _2: i.Pattern) extends i.And

  case class Or(_1: i.Pattern, _2: i.Pattern) extends i.Or

  case class Not(_1: i.Pattern) extends i.Not

  case class Implies(_1: i.Pattern, _2: i.Pattern) extends i.Implies

  case class Exists(_1: i.Variable, _2: i.Pattern) extends i.Exists

  case class ForAll(_1: i.Variable, _2: i.Pattern) extends i.ForAll

  case class Next(_1: i.Pattern) extends i.Next

  case class Rewrite(_1: i.Pattern, _2: i.Pattern) extends i.Rewrite

  case class Equals(_1: i.Pattern, _2: i.Pattern) extends i.Equals

}

object DefaultBuilders extends Build.Builders {

  import org.kframework.minikore.{MiniKore => m}

  override def Variable(_1: i.Name, _2: i.Sort): i.Variable = m.Variable(_1, _2)

  override def DomainValue(_1: i.Label, _2: i.Value): i.DomainValue = m.DomainValue(_1, _2)

  override def Top(): i.Top = m.Top()

  override def Bottom(): i.Bottom = m.Bottom()

  override def Not(_1: i.Pattern): i.Not = m.Not(_1)

  override def Next(_1: i.Pattern): i.Next = m.Next(_1)

  override def And(_1: i.Pattern, _2: i.Pattern): i.And = m.And(_1, _2)

  override def Or(_1: i.Pattern, _2: i.Pattern): i.Or = m.Or(_1, _2)

  override def Implies(_1: i.Pattern, _2: i.Pattern): i.Implies = m.Implies(_1, _2)

  override def Equals(_1: i.Pattern, _2: i.Pattern): i.Equals = m.Equals(_1, _2)

  override def Exists(_1: i.Variable, _2: i.Pattern): i.Exists = m.Exists(_1, _2)

  override def ForAll(_1: i.Variable, _2: i.Pattern): i.ForAll = m.ForAll(_1, _2)

  override def Rewrite(_1: i.Pattern, _2: i.Pattern): i.Rewrite = m.Rewrite(_1, _2)

  override def Application(_1: i.Label, args: Seq[i.Pattern]): m.Application = m.Application(_1, args)
}


