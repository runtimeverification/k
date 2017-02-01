package org.kframework.minikore

object MiniKoreInterface {

  // View

  trait Ast

  trait Leaf extends Ast

  trait Node[T <: Ast] extends Ast {
    def args: Seq[T]
  }

  trait Node1[T <: Ast] extends Ast {
    def p: T
  }

  trait Node2[T <: Ast] extends Ast {
    def p: T
    def q: T
  }

  trait NodeV[T <: Ast, V <: Leaf] extends Ast {
    def v: V
    def p: T
  }

  // Interface

  trait Pattern extends Ast

  trait Variable extends Pattern with Leaf {
    def name: String
    def sort: String
  }

  trait Application extends Pattern with Node[Pattern] {
    def label: String
    def args: Seq[Pattern]
  }

  trait DomainValue extends Pattern with Leaf {
    def label: String
    def value: String
  }

  trait True extends Pattern with Leaf

  trait False extends Pattern with Leaf

  trait And extends Pattern with Node2[Pattern] {
    def p: Pattern
    def q: Pattern
  }

  trait Or extends Pattern with Node2[Pattern] {
    def p: Pattern
    def q: Pattern
  }

  trait Not extends Pattern with Node1[Pattern] {
    def p: Pattern
  }

  trait Implies extends Pattern with Node2[Pattern] {
    def p: Pattern
    def q: Pattern
  }

  trait Exists extends Pattern with NodeV[Pattern, Variable] {
    def v: Variable
    def p: Pattern
  }

  trait ForAll extends Pattern with NodeV[Pattern, Variable] {
    def v: Variable
    def p: Pattern
  }

  trait Next extends Pattern with Node1[Pattern] {
    def p: Pattern
  }

  trait Rewrite extends Pattern with Node2[Pattern] {
    def p: Pattern
    def q: Pattern
  }

  trait Equal extends Pattern with Node2[Pattern] {
    def p: Pattern
    def q: Pattern
  }

  // Constructor

  trait Constructor[P <: Pattern, V <: Variable] {
    def Variable(name: String, sort: String): P
    def Application(label: String, args: Seq[P]): P
    def DomainValue(label: String, value: String): P
    def True(): P
    def False(): P
    def And(p: P, q: P): P
    def Or(p: P, q: P): P
    def Not(p: P): P
    def Implies(p: P, q: P): P
    def Exists(v: V, p: P): P
    def ForAll(v: V, p: P): P
    def Next(p: P): P
    def Rewrite(p: P, q: P): P
    def Equal(p: P, q: P): P
  }

}
