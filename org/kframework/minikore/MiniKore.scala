package org.kframework.minikore

import org.kframework.minikore.{MiniKoreInterface => i}

import scala.collection._

/** Algebraic data type of MiniKore. */
object MiniKore extends i.Constructor {

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
  case class Variable(name: String, sort: String) extends Pattern with i.Variable {
    override def constructor = Variable
  }
  case class Application(label: String, args: Seq[Pattern]) extends Pattern with i.Application {
    override def constructor = Application
  }
  case class DomainValue(label: String, value: String) extends Pattern with i.DomainValue {
    override def constructor = DomainValue
  }
  //
  case class True() extends Pattern with i.True {
    override def constructor = True
  }
  case class False() extends Pattern with i.False {
    override def constructor = False
  }
  //
  case class And(p: Pattern, q: Pattern) extends Pattern with i.And {
    override def constructor = And
  }
  case class Or(p: Pattern, q: Pattern) extends Pattern with i.Or {
    override def constructor = Or
  }
  case class Not(p: Pattern) extends Pattern with i.Not {
    override def constructor = Not
  }
  case class Implies(p: Pattern, q: Pattern) extends Pattern with i.Implies {
    override def constructor = Implies
  }
  case class Exists(v: Variable, p: Pattern) extends Pattern with i.Exists {
    override def constructor = Exists
  }
  case class ForAll(v: Variable, p: Pattern) extends Pattern with i.ForAll {
    override def constructor = ForAll
  }
  case class Next(p: Pattern) extends Pattern with i.Next {
    override def constructor = Next
  }
  case class Rewrite(p: Pattern, q: Pattern) extends Pattern with i.Rewrite {
    override def constructor = Rewrite
  }
  case class Equal(p: Pattern, q: Pattern) extends Pattern with i.Equal {
    override def constructor = Equal
  }

  object Variable    extends i.VariableConstructor {
  //override def apply(name: String, sort: String): i.Variable
  }
  object Application extends i.ApplicationConstructor {
    override def apply(label: String, args: Seq[i.Pattern]): i.Application = Application(label, args.asInstanceOf[Seq[Pattern]])
  }
  object DomainValue extends i.DomainValueConstructor {
  //override def apply(label: String, value: String): i.DomainValue
  }
  object True        extends i.Node0Constructor[i.True] {
  //override def apply(): i.True
  }
  object False       extends i.Node0Constructor[i.False] {
  //override def apply(): i.False
  }
  object And         extends i.Node2Constructor[i.And] {
    override def apply(p: i.Pattern, q: i.Pattern): i.And = And(p.asInstanceOf[Pattern], q.asInstanceOf[Pattern])
  }
  object Or          extends i.Node2Constructor[i.Or] {
    override def apply(p: i.Pattern, q: i.Pattern): i.Or = Or(p.asInstanceOf[Pattern], q.asInstanceOf[Pattern])
  }
  object Not         extends i.Node1Constructor[i.Not] {
    override def apply(p: i.Pattern): i.Not = Not(p.asInstanceOf[Pattern])
  }
  object Implies     extends i.Node2Constructor[i.Implies] {
    override def apply(p: i.Pattern, q: i.Pattern): i.Implies = Implies(p.asInstanceOf[Pattern], q.asInstanceOf[Pattern])
  }
  object Exists      extends i.NodeVConstructor[i.Exists] {
    override def apply(v: i.Variable, p: i.Pattern): i.Exists = Exists(v.asInstanceOf[Variable], p.asInstanceOf[Pattern])
  }
  object ForAll      extends i.NodeVConstructor[i.ForAll] {
    override def apply(v: i.Variable, p: i.Pattern): i.ForAll = ForAll(v.asInstanceOf[Variable], p.asInstanceOf[Pattern])
  }
  object Next        extends i.Node1Constructor[i.Next] {
    override def apply(p: i.Pattern): i.Next = Next(p.asInstanceOf[Pattern])
  }
  object Rewrite     extends i.Node2Constructor[i.Rewrite] {
    override def apply(p: i.Pattern, q: i.Pattern): i.Rewrite = Rewrite(p.asInstanceOf[Pattern], q.asInstanceOf[Pattern])
  }
  object Equal       extends i.Node2Constructor[i.Equal] {
    override def apply(p: i.Pattern, q: i.Pattern): i.Equal = Equal(p.asInstanceOf[Pattern], q.asInstanceOf[Pattern])
  }
}
