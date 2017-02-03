package org.kframework.minikore

import org.kframework.minikore.{MiniKoreInterface => i}

import scala.collection._

/** Algebraic data type of MiniKore. */
object MiniKore {

  //Default Implementation

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

  case class Application(label: String, args: Seq[Pattern]) extends Pattern with i.Application {
    override def children: Seq[Pattern] = args

    override def childrenAsSeq: Seq[Pattern] = children
  }

  case class DomainValue(label: String, value: String) extends Pattern with i.DomainValue

  case class True() extends Pattern with i.True

  case class False() extends Pattern with i.False

  case class And(p: Pattern, q: Pattern) extends Pattern with i.And {
    override def children: (Pattern, Pattern) = (p, q)

    override def childrenAsSeq: Seq[Pattern] = Seq(p, q)
  }

  case class Or(p: Pattern, q: Pattern) extends Pattern with i.Or {
    override def children: (Pattern, Pattern) = (p, q)

    override def childrenAsSeq: Seq[Pattern] = Seq(p, q)
  }

  case class Not(p: Pattern) extends Pattern with i.Not {
    override def children: Pattern = p

    override def childrenAsSeq: Seq[Pattern] = Seq(p)
  }

  case class Implies(p: Pattern, q: Pattern) extends Pattern with i.Implies {
    override def children: (Pattern, Pattern) = (p, q)

    override def childrenAsSeq: Seq[Pattern] = Seq(p, q)
  }

  case class Exists(v: Variable, p: Pattern) extends Pattern with i.Exists {
    override def children: (Variable, Pattern) = (v, p)

    override def childrenAsSeq: Seq[Pattern] = Seq(v, p)

  }

  case class ForAll(v: Variable, p: Pattern) extends Pattern with i.ForAll {
    override def children: (Variable, Pattern) = (v, p)

    override def childrenAsSeq: Seq[Pattern] = Seq(v, p)
  }

  case class Next(p: Pattern) extends Pattern with i.Next {
    override def children: Pattern = p

    override def childrenAsSeq: Seq[Pattern] = Seq(p)
  }

  case class Rewrite(p: Pattern, q: Pattern) extends Pattern with i.Rewrite {
    override def children: (Pattern, Pattern) = (p, q)

    override def childrenAsSeq: Seq[Pattern] = Seq(p, q)
  }

  case class Equals(p: Pattern, q: Pattern) extends Pattern with i.Equals {
    override def children: (Pattern, Pattern) = (p, q)

    override def childrenAsSeq: Seq[Pattern] = Seq(p, q)
  }

}
