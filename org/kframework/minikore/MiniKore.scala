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

  case class Variable(name: String, sort: String) extends i.Variable {
    override def construct = Constructors.Variable
  }

  case class Application(label: String, args: Seq[i.Pattern]) extends i.Application {
    override def construct = Constructors.Application
  }

  case class DomainValue(label: String, value: String) extends i.DomainValue {
    override def construct = Constructors.DomainValue
  }

  case class True() extends i.True {
    override def construct = Constructors.True
  }

  case class False() extends i.False {
    override def construct = Constructors.False
  }

  case class And(p: i.Pattern, q: i.Pattern) extends i.And {
    override def construct = Constructors.And
  }

  case class Or(p: i.Pattern, q: i.Pattern) extends i.Or {
    override def construct = Constructors.Or
  }

  case class Not(p: i.Pattern) extends i.Not {
    override def construct = Constructors.Not
  }

  case class Implies(p: i.Pattern, q: i.Pattern) extends i.Implies {
    override def construct = Constructors.Implies
  }

  case class Exists(v: i.Variable, p: i.Pattern) extends i.Exists {
    override def construct = Constructors.Exists
  }

  case class ForAll(v: i.Variable, p: i.Pattern) extends i.ForAll {
    override def construct = Constructors.ForAll
  }

  case class Next(p: i.Pattern) extends i.Next {
    override def construct = Constructors.Next
  }

  case class Rewrite(p: i.Pattern, q: i.Pattern) extends i.Rewrite {
    override def construct = Constructors.Rewrite
  }

  case class Equals(p: i.Pattern, q: i.Pattern) extends i.Equals {
    override def construct = Constructors.Equals
  }

}

object Constructors extends FactoryInterface {
  def Application(label: String, args: Seq[i.Pattern]): MiniKore.Application = MiniKore.Application(label, args)

  def Variable(name: String, sort: String): MiniKore.Variable = MiniKore.Variable(name, sort)

  def DomainValue(label: String, value: String): MiniKore.DomainValue = MiniKore.DomainValue(label, value)

  def True(): MiniKore.True = MiniKore.True()

  def False(): MiniKore.False = MiniKore.False()

  def And(p: i.Pattern, q: i.Pattern): MiniKore.And = MiniKore.And(p, q)

  def Or(p: i.Pattern, q: i.Pattern): MiniKore.Or = MiniKore.Or(p, q)

  def Not(p: i.Pattern): MiniKore.Not = MiniKore.Not(p)

  def Implies(p: i.Pattern, q: i.Pattern): MiniKore.Implies = MiniKore.Implies(p, q)

  def Exists(v: i.Variable, p: i.Pattern): MiniKore.Exists = MiniKore.Exists(v, p)

  def ForAll(v: i.Variable, p: i.Pattern): MiniKore.ForAll = MiniKore.ForAll(v, p)

  def Next(p: i.Pattern): MiniKore.Next = MiniKore.Next(p)

  def Rewrite(p: i.Pattern, q: i.Pattern): MiniKore.Rewrite = MiniKore.Rewrite(p, q)

  def Equals(p: i.Pattern, q: i.Pattern): MiniKore.Equals = MiniKore.Equals(p, q)
}
