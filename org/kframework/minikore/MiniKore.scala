package org.kframework.minikore

import org.kframework.minikore.{MiniKoreInterface => i}

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


  case class Variable(name: String, sort: String) extends i.Pattern with i.Variable

  case class Application(label: String, args: Seq[i.Pattern]) extends i.Pattern with i.Application {
    override def childrenAsSeq = args

    override def children = args
  }


  case class DomainValue(label: String, value: String) extends i.Pattern with i.DomainValue

  case class True() extends i.Pattern with i.True

  case class False() extends i.Pattern with i.False

  case class And(p: i.Pattern, q: i.Pattern) extends i.Pattern with i.And {
    override def children: (i.Pattern, i.Pattern) = (p, q)

    override def childrenAsSeq: Seq[i.Pattern] = Seq(p, q)
  }

  case class Or(p: i.Pattern, q: i.Pattern) extends i.Pattern with i.Or {
    override def children: (i.Pattern, i.Pattern) = (p, q)

    override def childrenAsSeq: Seq[i.Pattern] = Seq(p, q)
  }

  case class Not(p: i.Pattern) extends i.Pattern with i.Not {
    override def children: i.Pattern = p

    override def childrenAsSeq: Seq[i.Pattern] = Seq(p)
  }

  case class Implies(p: i.Pattern, q: i.Pattern) extends i.Pattern with i.Implies {
    override def children: (i.Pattern, i.Pattern) = (p, q)

    override def childrenAsSeq: Seq[i.Pattern] = Seq(p, q)
  }

  case class Exists(v: Variable, p: i.Pattern) extends i.Pattern with i.Exists {
    override def children: (Variable, i.Pattern) = (v, p)

    override def childrenAsSeq: Seq[i.Pattern] = Seq(v, p)

  }

  case class ForAll(v: Variable, p: i.Pattern) extends i.Pattern with i.ForAll {
    override def children: (Variable, i.Pattern) = (v, p)

    override def childrenAsSeq: Seq[i.Pattern] = Seq(v, p)
  }

  case class Next(p: i.Pattern) extends i.Pattern with i.Next {
    override def children: i.Pattern = p

    override def childrenAsSeq: Seq[i.Pattern] = Seq(p)
  }

  case class Rewrite(p: i.Pattern, q: i.Pattern) extends i.Pattern with i.Rewrite {
    override def children: (i.Pattern, i.Pattern) = (p, q)

    override def childrenAsSeq: Seq[i.Pattern] = Seq(p, q)
  }

  case class Equals(p: i.Pattern, q: i.Pattern) extends i.Pattern with i.Equals {
    override def children: (i.Pattern, i.Pattern) = (p, q)

    override def childrenAsSeq: Seq[i.Pattern] = Seq(p, q)
  }

}
