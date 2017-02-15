package org.kframework.minikore


import org.kframework.minikore.PatternInterface.{Not, Variable, _}
import org.kframework.minikore.TreeInterface._
import org.kframework.minikore.{PatternInterface => i}

import scala.Seq
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
    override def build = Constructors.VariableBuilder
  }


  case class Application(label: String, args: Seq[i.Pattern]) extends i.Application {
    override def build: (Seq[_ <: AST]) => LabelledNode[String, i.Application] = { (nArgs: Seq[_ <: AST]) =>
      val cArgs: Seq[i.Pattern] = nArgs.map(_.asInstanceOf[i.Pattern])
      Constructors.Application(label, cArgs)
    }
  }

  case class DomainValue(label: String, value: String) extends i.DomainValue {
    override def build: LeafBuilder[(String, String)] = Constructors.DomainValueBuilder
  }

  case class True() extends i.True {
    override def build: Node0Builder[i.True] = Constructors.TrueBuilder
  }

  case class False() extends i.False {
    override def build: Node0Builder[i.False] = Constructors.FalseBuilder
  }

  case class And(p: i.Pattern, q: i.Pattern) extends i.And {
    override def build: Node2Builder[i.Pattern, i.Pattern, i.And] = Constructors.AndBuilder
  }

  case class Or(p: i.Pattern, q: i.Pattern) extends i.Or {
    override def build: Node2Builder[i.Pattern, i.Pattern, i.Or] = Constructors.OrBuilder
  }

  case class Not(p: i.Pattern) extends i.Not {
    override def build: Node1Builder[i.Pattern, i.Not] = Constructors.NotBuilder
  }


  case class Implies(p: i.Pattern, q: i.Pattern) extends i.Implies {
    override def build: Node2Builder[i.Pattern, i.Pattern, i.Implies] = Constructors.ImpliesBuilder
  }

  case class Exists(v: i.Variable, p: i.Pattern) extends i.Exists {
    override def build: Node2BinderBuilder[i.Variable, i.Pattern, i.Exists] = Constructors.ExistsBuilder
  }

  case class ForAll(v: i.Variable, p: i.Pattern) extends i.ForAll {
    override def build: Node2BinderBuilder[i.Variable, i.Pattern, i.ForAll] = Constructors.ForAllBuilder
  }

  case class Next(p: i.Pattern) extends i.Next {
    override def build: Node1Builder[i.Pattern, i.Next] = Constructors.NextBuilder
  }

  case class Rewrite(p: i.Pattern, q: i.Pattern) extends i.Rewrite {
    override def build: Node2Builder[i.Pattern, i.Pattern, i.Rewrite] = Constructors.RewriteBuilder
  }

  case class Equals(p: i.Pattern, q: i.Pattern) extends i.Equals {
    override def build: Node2Builder[i.Pattern, i.Pattern, i.Equals] = Constructors.EqualsBuilder
  }

}

object Constructors extends FactoryInterface {

  import org.kframework.minikore.{TreeInterface => t}

  object VariableBuilder extends t.LeafBuilder[(String, String)] {
    override def apply(contents: (String, String)) = MiniKore.Variable(contents._1, contents._2)
  }

  def Variable(name: String, sort: String): MiniKore.Variable = MiniKore.Variable(name, sort)

  def Application(label: String, args: Seq[i.Pattern]): MiniKore.Application = MiniKore.Application(label, args)

  object DomainValueBuilder extends t.LeafBuilder[(String, String)] {
    override def apply(contents: (String, String)): Leaf[(String, String)] = MiniKore.DomainValue(contents._1, contents._2)
  }

  def DomainValue(label: String, value: String): MiniKore.DomainValue = MiniKore.DomainValue(label, value)

  object TrueBuilder extends t.Node0Builder[i.True] {
    override def apply(): Node[i.True] = MiniKore.True()
  }

  def True(): MiniKore.True = MiniKore.True()

  object FalseBuilder extends t.Node0Builder[i.False] {
    override def apply(): Node[i.False] = MiniKore.False()
  }

  def False(): MiniKore.False = MiniKore.False()

  object AndBuilder extends t.Node2Builder[i.Pattern, i.Pattern, i.And] {
    override def apply(p: Pattern, q: Pattern): Node2[Pattern, Pattern, i.And] = MiniKore.And(p, q)
  }

  def And(p: i.Pattern, q: i.Pattern): MiniKore.And = MiniKore.And(p, q)

  object OrBuilder extends t.Node2Builder[i.Pattern, i.Pattern, i.Or] {
    override def apply(p: Pattern, q: Pattern): Node2[Pattern, Pattern, i.Or] = MiniKore.Or(p, q)
  }

  def Or(p: i.Pattern, q: i.Pattern): MiniKore.Or = MiniKore.Or(p, q)

  object NotBuilder extends t.Node1Builder[i.Pattern, i.Not] {
    override def apply(p: Pattern): Node1[Pattern, Not] = MiniKore.Not(p)
  }

  def Not(p: i.Pattern): MiniKore.Not = MiniKore.Not(p)

  object ImpliesBuilder extends t.Node2Builder[i.Pattern, i.Pattern, i.Implies] {
    override def apply(p: Pattern, q: Pattern): Node2[i.Pattern, i.Pattern, i.Implies] = MiniKore.Implies(p, q)
  }

  def Implies(p: i.Pattern, q: i.Pattern): MiniKore.Implies = MiniKore.Implies(p, q)

  object ExistsBuilder extends Node2BinderBuilder[i.Variable, i.Pattern, i.Exists] {
    override def apply(v: Variable, p: Pattern): Node2Binder[i.Variable, i.Pattern, i.Exists] = MiniKore.Exists(v, p)
  }

  def Exists(v: i.Variable, p: i.Pattern): MiniKore.Exists = MiniKore.Exists(v, p)

  object ForAllBuilder extends Node2BinderBuilder[i.Variable, i.Pattern, i.ForAll] {
    override def apply(v: Variable, p: Pattern): Node2Binder[Variable, Pattern, ForAll] = MiniKore.ForAll(v, p)
  }

  def ForAll(v: i.Variable, p: i.Pattern): MiniKore.ForAll = MiniKore.ForAll(v, p)

  object NextBuilder extends t.Node1Builder[i.Pattern, i.Next] {
    override def apply(p: Pattern): Node1[i.Pattern, i.Next] = MiniKore.Next(p)
  }

  def Next(p: i.Pattern): MiniKore.Next = MiniKore.Next(p)

  object RewriteBuilder extends t.Node2Builder[i.Pattern, i.Pattern, i.Rewrite] {
    override def apply(p: Pattern, q: Pattern): Node2[Pattern, Pattern, i.Rewrite] = MiniKore.Rewrite(p, q)
  }

  def Rewrite(p: i.Pattern, q: i.Pattern): MiniKore.Rewrite = MiniKore.Rewrite(p, q)

  object EqualsBuilder extends t.Node2Builder[i.Pattern, i.Pattern, i.Equals] {
    override def apply(p: Pattern, q: Pattern): Node2[i.Pattern, i.Pattern, i.Equals] = MiniKore.Equals(p, q)
  }

  def Equals(p: i.Pattern, q: i.Pattern): MiniKore.Equals = MiniKore.Equals(p, q)
}
