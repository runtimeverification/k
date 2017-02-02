package org.kframework.minikore

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

  sealed trait Pattern extends i.Pattern
  case class Variable(name: String, sort: String) extends Pattern with i.Variable {
    override def constructor = Variable.asInstanceOf[i.VariableConstructor]
  }
  case class Application(label: String, args: Seq[Pattern]) extends Pattern with i.Application {
    override def constructor = Application.asInstanceOf[i.ApplicationConstructor]
  }
  case class DomainValue(label: String, value: String) extends Pattern with i.DomainValue {
    override def constructor = DomainValue.asInstanceOf[i.DomainValueConstructor]
  }
  //
  case class True() extends Pattern with i.True {
    override def constructor = True.asInstanceOf[i.Node0Constructor[i.True]]
  }
  case class False() extends Pattern with i.False {
    override def constructor = False.asInstanceOf[i.Node0Constructor[i.False]]
  }
  //
  case class And(p: Pattern, q: Pattern) extends Pattern with i.And {
    override def constructor = And.asInstanceOf[i.Node2Constructor[i.And]]
  }
  case class Or(p: Pattern, q: Pattern) extends Pattern with i.Or {
    override def constructor = Or.asInstanceOf[i.Node2Constructor[i.Or]]
  }
  case class Not(p: Pattern) extends Pattern with i.Not {
    override def constructor = Not.asInstanceOf[i.Node1Constructor[i.Not]]
  }
  case class Implies(p: Pattern, q: Pattern) extends Pattern with i.Implies {
    override def constructor = Implies.asInstanceOf[i.Node2Constructor[i.Implies]]
  }
  case class Exists(v: Variable, p: Pattern) extends Pattern with i.Exists {
    override def constructor = Exists.asInstanceOf[i.NodeVConstructor[i.Exists]]
  }
  case class ForAll(v: Variable, p: Pattern) extends Pattern with i.ForAll {
    override def constructor = ForAll.asInstanceOf[i.NodeVConstructor[i.ForAll]]
  }
  case class Next(p: Pattern) extends Pattern with i.Next {
    override def constructor = Next.asInstanceOf[i.Node1Constructor[i.Next]]
  }
  case class Rewrite(p: Pattern, q: Pattern) extends Pattern with i.Rewrite {
    override def constructor = Rewrite.asInstanceOf[i.Node2Constructor[i.Rewrite]]
  }
  case class Equal(p: Pattern, q: Pattern) extends Pattern with i.Equal {
    override def constructor = Equal.asInstanceOf[i.Node2Constructor[i.Equal]]
  }

}
