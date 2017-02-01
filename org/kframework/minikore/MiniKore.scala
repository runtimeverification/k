package org.kframework.minikore

import org.kframework.minikore.MiniKoreInterface.Ast
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
  case class Variable(name: String, sort: String) extends Pattern with i.Variable[Pattern] { override def constructor: (String, String) => Pattern = Variable.apply }
  case class Application(label: String, args: Seq[Pattern]) extends Pattern with i.Application[Pattern] { override def constructor: (String, Seq[Pattern]) => Pattern = Application.apply }
  case class DomainValue(label: String, value: String) extends Pattern with i.DomainValue[Pattern] { override def constructor: (String, String) => Pattern = DomainValue.apply }
  //
  case class True() extends Pattern with i.True[Pattern] { override def constructor: () => Pattern = True.apply }
  case class False() extends Pattern with i.False[Pattern] { override def constructor: () => Pattern = False.apply }
  //
  case class And(p: Pattern, q: Pattern) extends Pattern with i.And[Pattern] { override def constructor: (Pattern, Pattern) => Pattern = And.apply }
  case class Or(p: Pattern, q: Pattern) extends Pattern with i.Or[Pattern] { override def constructor: (Pattern, Pattern) => Pattern = Or.apply }
  case class Not(p: Pattern) extends Pattern with i.Not[Pattern] { override def constructor: Pattern => Pattern = Not.apply }
  case class Implies(p: Pattern, q: Pattern) extends Pattern with i.Implies[Pattern] { override def constructor: (Pattern, Pattern) => Pattern = Implies.apply }
  case class Exists(v: Variable, p: Pattern) extends Pattern with i.Exists[Variable, Pattern] { override def constructor: (Variable, Pattern) => Pattern = Exists.apply }
  case class ForAll(v: Variable, p: Pattern) extends Pattern with i.ForAll[Variable, Pattern] { override def constructor: (Variable, Pattern) => Pattern = ForAll.apply }
  //
  case class Next(p: Pattern) extends Pattern with i.Next[Pattern] { override def constructor: Pattern => Pattern = Next.apply }
  case class Rewrite(p: Pattern, q: Pattern) extends Pattern with i.Rewrite[Pattern] { override def constructor: (Pattern, Pattern) => Pattern = Rewrite.apply }
  case class Equal(p: Pattern, q: Pattern) extends Pattern with i.Equal[Pattern] { override def constructor: (Pattern, Pattern) => Pattern = Equal.apply }

}
