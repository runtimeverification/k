package org.kframework.minikore

import org.kframework.minikore.{MiniKoreInterface => i}

import scala.collection._

/** Algebraic data type of MiniKore. */
object MiniKore {

  type Attributes = Seq[Pattern]

  case class Definition(modules: Seq[Module], att: Attributes)
  case class Module(name: String, sentences: Seq[Sentence], att: Attributes)

  sealed trait Sentence
  case class Import(name: String, att: Attributes) extends Sentence
  case class SortDeclaration(sort: String, att: Attributes) extends Sentence
  case class SymbolDeclaration(sort: String, label: String, args: Seq[String], att: Attributes) extends Sentence
  case class Rule(pattern: Pattern, att: Attributes) extends Sentence
  case class Axiom(pattern: Pattern, att: Attributes) extends Sentence

  sealed trait Pattern extends i.Pattern
  case class Variable(name: String, sort: String) extends Pattern with i.Variable
  case class Application(label: String, args: Seq[Pattern]) extends Pattern with i.Application
  case class DomainValue(label: String, value: String) extends Pattern with i.DomainValue
  //
  case class True() extends Pattern with i.True
  case class False() extends Pattern with i.False
  //
  case class And(p: Pattern, q: Pattern) extends Pattern with i.And
  case class Or(p: Pattern, q: Pattern) extends Pattern with i.Or
  case class Not(p: Pattern) extends Pattern with i.Not
  case class Implies(p: Pattern, q: Pattern) extends Pattern with i.Implies
  case class Exists(v: Variable, p: Pattern) extends Pattern with i.Exists
  case class ForAll(v: Variable, p: Pattern) extends Pattern with i.ForAll
  //
  case class Next(p: Pattern) extends Pattern with i.Next
  case class Rewrite(p: Pattern, q: Pattern) extends Pattern with i.Rewrite
  case class Equal(p: Pattern, q: Pattern) extends Pattern with i.Equal

  object Constructor extends i.Constructor[Pattern, Variable] {
    override def Variable(name: String, sort: String) = MiniKore.Variable(name, sort)
    override def Application(label: String, args: Seq[Pattern]) = MiniKore.Application(label, args)
    override def DomainValue(label: String, value: String) = MiniKore.DomainValue(label, value)
    override def True() = MiniKore.True()
    override def False() = MiniKore.False()
    override def And(p: Pattern, q: Pattern) = MiniKore.And(p,q)
    override def Or(p: Pattern, q: Pattern) = MiniKore.Or(p,q)
    override def Not(p: Pattern) = MiniKore.Not(p)
    override def Implies(p: Pattern, q: Pattern) = MiniKore.Implies(p, q)
    override def Exists(v: Variable, p: Pattern) = MiniKore.Exists(v,p)
    override def ForAll(v: Variable, p: Pattern) = MiniKore.ForAll(v,p)
    override def Next(p: Pattern) = MiniKore.Next(p)
    override def Rewrite(p: Pattern, q: Pattern) = MiniKore.Rewrite(p, q)
    override def Equal(p: Pattern, q: Pattern) = MiniKore.Equal(p, q)
  }

}
