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

  case class Variable(name: String, sort: i.Sort) extends i.Variable {
    override def build: i.VariableBuilder = Variable.apply
  }

  case class Application(label: String, args: Seq[i.Pattern]) extends i.Application {
    override def build = Application(label, _: Seq[i.Pattern])
  }

  case class DomainValue(label: String, value: String) extends i.DomainValue {
    override def build: i.DomainValueBuilder = DomainValue.apply
  }

  case class True() extends i.True {
    override def build: i.TrueBuilder = () => True()
  }


  case class False() extends i.False {
    override def build: i.FalseBuilder = () => False()
  }

  case class And(override val p: i.Pattern, override val q: i.Pattern) extends i.And {
    override def build: i.AndBuilder = And.apply
  }

  case class Or(p: i.Pattern, q: i.Pattern) extends i.Or {
    override def build: i.OrBuilder = Or.apply
  }

  case class Not(p: i.Pattern) extends i.Not {
    override def build: i.NotBuilder = Not.apply
  }


  case class Implies(p: i.Pattern, q: i.Pattern) extends i.Implies {
    override def build: i.ImpliesBuilder = Implies.apply
  }

  case class Exists(v: i.Variable, p: i.Pattern) extends i.Exists {
    override def build: i.ExistsBuilder = Exists.apply
  }

  case class ForAll(v: i.Variable, p: i.Pattern) extends i.ForAll {
    override def build: i.ForAllBuilder = ForAll.apply
  }

  case class Next(p: i.Pattern) extends i.Next {
    override def build: i.NextBuilder = Next.apply
  }

  case class Rewrite(p: i.Pattern, q: i.Pattern) extends i.Rewrite {
    override def build: i.RewriteBuilder = Rewrite.apply
  }

  case class Equals(p: i.Pattern, q: i.Pattern) extends i.Equals {
    override def build: i.EqualsBuilder = Equals.apply
  }

  object ApplicationBuilder extends i.ApplicationBuilder {
    def apply(label: String, children: Seq[i.Pattern]) = Application(label, children)
  }

}

object DefaultBuilders {

  import org.kframework.minikore.{MiniKore => m}

  def build: Builders = Builders(m.Variable.apply, m.DomainValue.apply, m.True().build, m.False().build,
    m.Not.apply, m.Next.apply, m.Exists.apply, m.ForAll.apply, m.And.apply, m.Or.apply, m.Implies.apply,
    m.Equals.apply, m.Rewrite.apply, m.ApplicationBuilder)

}

