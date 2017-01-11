package org.kframework.minikore

import scala.collection._

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

  sealed trait Pattern
  case class Variable(name: String, sort: String) extends Pattern
  case class Application(label: String, args: Seq[Pattern]) extends Pattern
  case class DomainValue(label: String, value: String) extends Pattern
  //
  case class True() extends Pattern
  case class False() extends Pattern
  //
  case class And(p: Pattern, q: Pattern) extends Pattern
  case class Or(p: Pattern, q: Pattern) extends Pattern
  case class Not(p: Pattern) extends Pattern
  case class Implies(p: Pattern, q: Pattern) extends Pattern
  case class Exists(v: Variable, p: Pattern) extends Pattern
  case class ForAll(v: Variable, p: Pattern) extends Pattern
  //
  case class Next(p: Pattern) extends Pattern
  case class Rewrite(p: Pattern, q: Pattern) extends Pattern
  case class Equal(p: Pattern, q: Pattern) extends Pattern

}
