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
    override def apply(name: String, sort: String): Variable = Variable(name, sort)
  }

  case class Application(label: String, args: Seq[i.Pattern]) extends i.Application {
    override def apply(label: String, children: Seq[i.Pattern]): Application =
      Application(label, children)
  }

  case class DomainValue(label: String, value: String) extends i.DomainValue {
    override def apply(label: String, value: String): DomainValue = DomainValue(label, value)
  }

  case class True() extends i.True {
    override def apply(): True = True()
  }

  case class False() extends i.False {
    override def apply(): i.Pattern = False()
  }

  case class And(p: i.Pattern, q: i.Pattern) extends i.And {
    override def apply(p: i.Pattern, q: i.Pattern): And = And(p, q)
  }

  case class Or(p: i.Pattern, q: i.Pattern) extends i.Or {
    override def apply(p: i.Pattern, q: i.Pattern): Or = Or(p, q)
  }

  case class Not(p: i.Pattern) extends i.Not {
    override def apply(p: i.Pattern): Not = Not(p)
  }

  case class Implies(p: i.Pattern, q: i.Pattern) extends i.Implies {
    override def apply(p: i.Pattern, q: i.Pattern): Implies = Implies(p, q)
  }

  case class Exists(v: i.Variable, p: i.Pattern) extends i.Exists {
    override def apply(v: i.Variable, p: i.Pattern): Exists = Exists(v, p)
  }

  case class ForAll(v: i.Variable, p: i.Pattern) extends i.ForAll {
    override def apply(v: i.Variable, p: i.Pattern): ForAll = ForAll(v, p)
  }

  case class Next(p: i.Pattern) extends i.Next {
    override def apply(p: i.Pattern): Next = Next(p)
  }

  case class Rewrite(p: i.Pattern, q: i.Pattern) extends i.Rewrite {
    override def apply(p: i.Pattern, q: i.Pattern): Rewrite = Rewrite(p, q)
  }

  case class Equals(p: i.Pattern, q: i.Pattern) extends i.Equals {
    override def apply(p: i.Pattern, q: i.Pattern): Equals = Equals(p, q)
  }

}

object DefaultBuilders extends Build.Builders {

  import org.kframework.minikore.{MiniKore => m}

  override def Variable(name: String, sort: i.Sort): i.Variable = m.Variable(name, sort)

  override def DomainValue(label: String, value: String): i.DomainValue = m.DomainValue(label, value)

  override def True(): i.True = m.True()

  override def False(): i.False = m.False()

  override def Not(p: i.Pattern): i.Not = m.Not(p)

  override def Next(p: i.Pattern): i.Next = m.Next(p)

  override def And(p: i.Pattern, q: i.Pattern): i.And = m.And(p, q)

  override def Or(p: i.Pattern, q: i.Pattern): i.Or = m.Or(p, q)

  override def Implies(p: i.Pattern, q: i.Pattern): i.Implies = m.Implies(p, q)

  override def Equals(p: i.Pattern, q: i.Pattern): i.Equals = m.Equals(p, q)

  override def Exists(v: i.Variable, p: i.Pattern): i.Exists = m.Exists(v, p)

  override def ForAll(v: i.Variable, p: i.Pattern): i.ForAll = m.ForAll(v, p)

  override def Rewrite(p: i.Pattern, q: i.Pattern): i.Rewrite = m.Rewrite(p, q)

  override def Application(s: String, args: Seq[i.Pattern]): m.Application = m.Application(s, args)
}


