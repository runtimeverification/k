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
    override def construct: (String, String) => Variable = {(name: String, sort: String) => new Variable(name, sort)}
  }

  case class Application(label: String, args: Seq[i.Pattern]) extends i.Application {
    override def construct: (String, Seq[i.Pattern]) => Application = {
      (label: String, args: Seq[i.Pattern]) =>
        new Application(label, args)
    }
  }

  case class DomainValue(label: String, value: String) extends i.DomainValue {
    override def construct: (String, String) => DomainValue = { (label: String, value: String) => new DomainValue(label, value) }
  }

  case class True() extends i.True {
    override def construct: (Seq[i.Pattern]) => True = { (args: Seq[i.Pattern]) =>
      assert(args.isEmpty)
      new True()
    }
  }

  case class False() extends i.False {
    override def construct: (Seq[i.Pattern]) => False = { (args: Seq[i.Pattern]) =>
      assert(args.isEmpty)
      new False()
    }
  }

  case class And(p: i.Pattern, q: i.Pattern) extends i.And {
    override def construct: Seq[i.Pattern] => And = { (args: Seq[i.Pattern]) =>
      assert(args.size == 2)
      new And(args(0), args(1))
    }
  }

  case class Or(p: i.Pattern, q: i.Pattern) extends i.Or {
    override def construct: Seq[i.Pattern] => Or = { (args: Seq[i.Pattern]) =>
      assert(args.size == 2)
      new Or(args(0), args(1))
    }
  }

  case class Not(p: i.Pattern) extends i.Not {
    override def construct: Seq[i.Pattern] => Not = { (args: Seq[i.Pattern]) =>
      assert(args.size == 1)
      new Not(args(0))
    }
  }


  case class Implies(p: i.Pattern, q: i.Pattern) extends i.Implies {
    override def construct: Seq[i.Pattern] => Implies = { (args: Seq[i.Pattern]) =>
      assert(args.size == 2)
      new Implies(args(0), args(1))
    }
  }

  case class Exists(v: i.Variable, p: i.Pattern) extends i.Exists {
    override def construct: Seq[i.Pattern] => Exists = {
      (args: Seq[i.Pattern]) =>
        assert(args.size == 2)
        args(0) match {
          case p: i.Variable => new Exists(p, args(1))
        }
    }
  }

  case class ForAll(v: i.Variable, p: i.Pattern) extends i.ForAll {
    override def construct: Seq[i.Pattern] => ForAll = {
      (args: Seq[i.Pattern]) =>
        assert(args.size == 2)
        args(0) match {
          case p: i.Variable => new ForAll(p, args(1))
        }
    }
  }

  case class Next(p: i.Pattern) extends i.Next {
    override def construct: Seq[i.Pattern] => Next = { (args: Seq[i.Pattern]) =>
      assert(args.size == 1)
      new Next(args(0))
    }
  }

  case class Rewrite(p: i.Pattern, q: i.Pattern) extends i.Rewrite {
    override def construct: Seq[i.Pattern] => Rewrite = { (args: Seq[i.Pattern]) =>
      assert(args.size == 2)
      new Rewrite(args(0), args(1))
    }
  }

  case class Equals(p: i.Pattern, q: i.Pattern) extends i.Equals {
    override def construct: Seq[i.Pattern] => Equals = { (args: Seq[i.Pattern]) =>
      assert(args.size == 2)
      new Equals(args(0), args(1))
    }
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
