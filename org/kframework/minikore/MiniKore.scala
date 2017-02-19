package org.kframework.minikore


import org.kframework.minikore.PatternInterface.Pattern
import org.kframework.minikore.TreeInterface._
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

  case class Variable(name: String, sort: i.Sort) extends i.Variable {
    override def build = DefaultBuilders.VariableBuilder
  }

  case class Application(label: String, args: Seq[i.Pattern]) extends i.Application {
    override def build = DefaultBuilders.ApplicationBuilder.curried.apply(label).asInstanceOf[LabelBuild[String, i.Pattern]]
  }


  case class DomainValue(label: String, value: String) extends i.DomainValue {
    override def build = DefaultBuilders.DomainValueBuilder
  }

  case class True() extends i.True {
    override def build = DefaultBuilders.TrueBuilder
  }

  case class False() extends i.False {
    override def build: Node0Builder[i.Pattern] = DefaultBuilders.FalseBuilder
  }

  case class And(override val p: i.Pattern, override val q: i.Pattern) extends i.And {
    override def build: Node2Builder[i.Pattern] = DefaultBuilders.AndBuilder
  }

  case class Or(p: i.Pattern, q: i.Pattern) extends i.Or {
    override def build: Node2Builder[i.Pattern] = DefaultBuilders.OrBuilder
  }

  case class Not(p: i.Pattern) extends i.Not {
    override def build: NodeBuilder[i.Pattern] = DefaultBuilders.NotBuilder
  }


  case class Implies(p: i.Pattern, q: i.Pattern) extends i.Implies {
    override def build: Node2Builder[i.Pattern] = DefaultBuilders.ImpliesBuilder
  }

  case class Exists(v: i.Variable, p: i.Pattern) extends i.Exists {
    override def build: Node2Builder[i.Pattern] = DefaultBuilders.ExistsBuilder
  }

  case class ForAll(v: i.Variable, p: i.Pattern) extends i.ForAll {
    override def build: Node2Builder[i.Pattern] = DefaultBuilders.ForAllBuilder
  }

  case class Next(p: i.Pattern) extends i.Next {
    override def build: NodeBuilder[i.Pattern] = DefaultBuilders.NextBuilder
  }

  case class Rewrite(p: i.Pattern, q: i.Pattern) extends i.Rewrite {
    override def build: Node2Builder[i.Pattern] = DefaultBuilders.RewriteBuilder
  }

  case class Equals(p: i.Pattern, q: i.Pattern) extends i.Equals {
    override def build: Node2Builder[i.Pattern] = DefaultBuilders.EqualsBuilder
  }

}

object DefaultBuilders {

  import org.kframework.minikore.{MiniKore => m}

  object VariableBuilder extends i.VariableBuilder {
    override def apply(contents: (String, i.Sort)) = m.Variable(contents._1, contents._2)
  }

  object DomainValueBuilder extends i.DomainValueBuilder {
    override def apply(contents: (String, String)) = m.DomainValue(contents._1, contents._2)
  }

  object AndBuilder extends i.AndBuilder {
    override def apply(v1: Pattern, v2: Pattern) = m.And(v1, v2)
  }

  object OrBuilder extends i.OrBuilder {
    override def apply(v1: Pattern, v2: Pattern) = m.Or(v1, v2)
  }

  object ImpliesBuilder extends i.ImpliesBuilder {
    override def apply(v1: Pattern, v2: Pattern) = m.Implies(v1, v2)
  }

  object RewriteBuilder extends i.RewriteBuilder {
    override def apply(v1: Pattern, v2: Pattern) = m.Rewrite(v1, v2)
  }

  object EqualsBuilder extends i.EqualsBuilder {
    override def apply(v1: Pattern, v2: Pattern) = m.Equals(v1, v2)
  }

  object NotBuilder extends i.NotBuilder {
    override def apply(v1: Pattern) = m.Not(v1)
  }

  object NextBuilder extends i.NextBuilder {
    override def apply(v1: Pattern) = m.Next(v1)
  }

  object TrueBuilder extends i.TrueBuilder {
    override def apply() = m.True()
  }

  object FalseBuilder extends i.FalseBuilder {
    override def apply() = m.False()
  }

  object ExistsBuilder extends i.ExistsBuilder {
    override def apply(v1: Pattern, v2: Pattern) = m.Exists(v1.asInstanceOf[i.Variable], v2)
  }

  object ForAllBuilder extends i.ForAllBuilder {
    override def apply(v1: Pattern, v2: Pattern) = m.ForAll(v1.asInstanceOf[i.Variable], v2)
  }

  object ApplicationBuilder extends i.ApplicationBuilder {
    override def apply(v1: String, v2: Seq[_ <: AST[Pattern]]) = {
      m.Application(v1, v2.map(_.asInstanceOf[i.Pattern]))
    }
  }

  def build: Builders = Builders(VariableBuilder, DomainValueBuilder, TrueBuilder, FalseBuilder,
    NotBuilder, NextBuilder, ExistsBuilder, ForAllBuilder, AndBuilder, OrBuilder, ImpliesBuilder, EqualsBuilder,
    RewriteBuilder, ApplicationBuilder)

}



