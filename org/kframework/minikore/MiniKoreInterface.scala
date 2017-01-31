package org.kframework.minikore

object MiniKoreInterface {

  trait Pattern

  trait Variable extends Pattern {
    def name: String
    def sort: String
  }

  trait Application extends Pattern {
    def label: String
    def args: Seq[Pattern]
  }

  trait DomainValue extends Pattern {
    def label: String
    def value: String
  }

  trait True extends Pattern

  trait False extends Pattern

  trait And extends Pattern {
    def p: Pattern
    def q: Pattern
  }

  trait Or extends Pattern {
    def p: Pattern
    def q: Pattern
  }

  trait Exists extends Pattern {
    def v: Variable
    def p: Pattern
  }

  trait Constructor[P <: Pattern, V <: Variable] {
    def Variable(name: String, sort: String): P
    def Application(label: String, args: Seq[P]): P
    def DomainValue(label: String, value: String): P
    def True(): P
    def False(): P
    def And(p: P, q: P): P
    def Or(p: P, q: P): P
    def Exists(v: V, p: P): P
  }

}
