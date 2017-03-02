package org.kframework.minikore.implementation

import org.kframework.minikore.interfaces.{build, pattern => i}

import scala.collection._

/** Algebraic data type of MiniKore. */
object MiniKore {

  /** A collection of classes that serve as the default implementation of the [[org.kframework.minikore.interfaces.pattern]] **/

  type Attributes = Seq[i.Pattern]

  case class Definition(modules: Seq[Module], att: Attributes)

  case class Module(name: String, sentences: Seq[Sentence], att: Attributes)

  sealed trait Sentence

  case class Import(name: String, att: Attributes) extends Sentence

  case class SortDeclaration(sort: String, att: Attributes) extends Sentence

  case class SymbolDeclaration(sort: String, label: String, args: Seq[String], att: Attributes) extends Sentence

  case class Rule(pattern: i.Pattern, att: Attributes) extends Sentence

  case class Axiom(pattern: i.Pattern, att: Attributes) extends Sentence

  case class Variable(_1: i.Name, _2: i.Sort) extends i.Variable {
    def apply(_1: i.Name, _2: i.Sort): Variable = new Variable(_1, _2)
  }

  case class DomainValue(_1: i.Label, _2: i.Value) extends i.DomainValue {
    def apply(_1: i.Label, _2: i.Value): DomainValue = DomainValue(_1, _2)
  }

  case class Application(_1: i.Label, args: Seq[i.Pattern]) extends i.Application {
    def apply(_1: i.Label, args: Seq[i.Pattern]): Application = Application(_1, args)
  }

  case class Top() extends i.Top {
    def apply(): Top = Top()
  }

  case class Bottom() extends i.Bottom {
    def apply(): Bottom = Bottom()
  }

  case class And(override val _1: i.Pattern, override val _2: i.Pattern) extends i.And {
    def apply(_1: i.Pattern, _2: i.Pattern): And = new And(_1, _2)
  }


  case class Or(_1: i.Pattern, _2: i.Pattern) extends i.Or {
    def apply(_1: i.Pattern, _2: i.Pattern): Or = Or(_1, _2)
  }

  case class Not(_1: i.Pattern) extends i.Not {
    def apply(_1: i.Pattern): Not = Not(_1)
  }

  case class Implies(_1: i.Pattern, _2: i.Pattern) extends i.Implies {
    def apply(_1: i.Pattern, _2: i.Pattern): Implies = Implies(_1, _2)
  }

  case class Exists(_1: i.Variable, _2: i.Pattern) extends i.Exists {
    def apply(_1: i.Variable, _2: i.Pattern): Exists = Exists(_1, _2)
  }

  case class ForAll(_1: i.Variable, _2: i.Pattern) extends i.ForAll {
    def apply(_1: i.Variable, _2: i.Pattern): ForAll = ForAll(_1, _2)
  }

  case class Next(_1: i.Pattern) extends i.Next {
    def apply(_1: i.Pattern): Next = Next(_1)
  }

  case class Rewrite(_1: i.Pattern, _2: i.Pattern) extends i.Rewrite {
    def apply(_1: i.Pattern, _2: i.Pattern): Rewrite = Rewrite(_1, _2)
  }

  case class Equals(_1: i.Pattern, _2: i.Pattern) extends i.Equals {
    def apply(_1: i.Pattern, _2: i.Pattern): Equals = Equals(_1, _2)
  }

}

/** Implementation of the [[org.kframework.minikore.interfaces.build.Builders]] **/
object DefaultBuilders extends build.Builders {

  import org.kframework.minikore.implementation.{MiniKore => m}

  def Variable(_1: i.Name, _2: i.Sort): i.Variable = m.Variable(_1, _2)

  def DomainValue(_1: i.Label, _2: i.Value): i.DomainValue = m.DomainValue(_1, _2)

  def Top(): i.Top = m.Top()

  def Bottom(): i.Bottom = m.Bottom()

  def Not(_1: i.Pattern): i.Not = m.Not(_1)

  def Next(_1: i.Pattern): i.Next = m.Next(_1)

  def And(_1: i.Pattern, _2: i.Pattern): i.And = new m.And(_1, _2)

  def Or(_1: i.Pattern, _2: i.Pattern): i.Or = m.Or(_1, _2)

  def Implies(_1: i.Pattern, _2: i.Pattern): i.Implies = m.Implies(_1, _2)

  def Equals(_1: i.Pattern, _2: i.Pattern): i.Equals = m.Equals(_1, _2)

  def Exists(_1: i.Variable, _2: i.Pattern): i.Exists = m.Exists(_1, _2)

  def ForAll(_1: i.Variable, _2: i.Pattern): i.ForAll = m.ForAll(_1, _2)

  def Rewrite(_1: i.Pattern, _2: i.Pattern): i.Rewrite = m.Rewrite(_1, _2)

  def Application(_1: i.Label, args: Seq[i.Pattern]): MiniKore.Application = m.Application(_1, args)
}


