package org.kframework.minikore

import org.kframework.minikore.MiniKoreInterface.{Ast, Node0Constructor}
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

  sealed trait Pattern extends i.Pattern_
  case class Variable(name: String, sort: String) extends Pattern with i.Variable[Pattern, String, String] {
    override def constructor = Variable.asInstanceOf[i.VariableConstructor[Pattern, String, String]]
  }
  case class Application(label: String, args: Seq[Pattern]) extends Pattern with i.Application[Pattern, String] {
    override def constructor = Application.asInstanceOf[i.ApplicationConstructor[Pattern, String]]
  }
  case class DomainValue(label: String, value: String) extends Pattern with i.DomainValue[Pattern, String, String] {
    override def constructor = DomainValue.asInstanceOf[i.DomainValueConstructor[Pattern, String, String]]
  }
  //
  case class True() extends Pattern with i.True[Pattern] {
    override def constructor = True.asInstanceOf[i.Node0Constructor[Pattern]]
  }
  case class False() extends Pattern with i.False[Pattern] {
    override def constructor = False.asInstanceOf[i.Node0Constructor[Pattern]]
  }
  //
  case class And(p: Pattern, q: Pattern) extends Pattern with i.And[Pattern] {
    override def constructor = And.asInstanceOf[i.Node2Constructor[Pattern, Pattern, Pattern]]
  }
  case class Or(p: Pattern, q: Pattern) extends Pattern with i.Or[Pattern] {
    override def constructor = Or.asInstanceOf[i.Node2Constructor[Pattern, Pattern, Pattern]]
  }
  case class Not(p: Pattern) extends Pattern with i.Not[Pattern] {
    override def constructor = Not.asInstanceOf[i.Node1Constructor[Pattern, Pattern]]
  }
  case class Implies(p: Pattern, q: Pattern) extends Pattern with i.Implies[Pattern] {
    override def constructor = Implies.asInstanceOf[i.Node2Constructor[Pattern, Pattern, Pattern]]
  }
  case class Exists(v: Variable, p: Pattern) extends Pattern with i.Exists[Pattern, Variable, String, String] {
    override def constructor = Exists.asInstanceOf[i.NodeVConstructor[Pattern, Variable, Pattern]]
  }
  case class ForAll(v: Variable, p: Pattern) extends Pattern with i.ForAll[Pattern, Variable, String, String] {
    override def constructor = ForAll.asInstanceOf[i.NodeVConstructor[Pattern, Variable, Pattern]]
  }
  case class Next(p: Pattern) extends Pattern with i.Next[Pattern] {
    override def constructor = Next.asInstanceOf[i.Node1Constructor[Pattern, Pattern]]
  }
  case class Rewrite(p: Pattern, q: Pattern) extends Pattern with i.Rewrite[Pattern] {
    override def constructor = Rewrite.asInstanceOf[i.Node2Constructor[Pattern, Pattern, Pattern]]
  }
  case class Equal(p: Pattern, q: Pattern) extends Pattern with i.Equal[Pattern] {
    override def constructor = Equal.asInstanceOf[i.Node2Constructor[Pattern, Pattern, Pattern]]
  }

//  object Variable extends i.VariableConstructor[Pattern, String, String]
//  object Application extends i.ApplicationConstructor[Pattern, String]
//  object DomainValue extends i.DomainValueConstructor[Pattern, String, String]
//  object True extends i.Node0Constructor[Pattern]

}
