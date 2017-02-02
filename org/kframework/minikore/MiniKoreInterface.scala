package org.kframework.minikore

object MiniKoreInterface {

  //

  sealed trait Ast

  // no sub-pattern
  trait Leaf extends Ast

  // symbol application
  trait Node[S] extends Ast {
    def label: S
  }

  // matching logic connectives

  trait Node0[T <: Ast] extends Ast {
    def constructor: Node0Constructor[T]
  }
  trait Node0Constructor[T <: Ast] {
    def apply(): T
  }

  trait Node1[T <: Ast, T1 <: Ast] extends Ast {
    def p: T1
    def constructor: Node1Constructor[T, T1]
  }
  trait Node1Constructor[T <: Ast, T1 <: Ast] {
    def apply(p: T1): T
  }

  trait Node2[T <: Ast, T1 <: Ast, T2 <: Ast] extends Ast {
    def p: T1
    def q: T2
    def constructor: Node2Constructor[T, T1, T2]
  }
  trait Node2Constructor[T <: Ast, T1 <: Ast, T2 <: Ast] {
    def apply(p: T1, q: T2): T
  }

  trait NodeV[T <: Ast, T1 <: Ast, T2 <: Ast] extends Ast {
    def v: T1
    def p: T2
    def constructor: NodeVConstructor[T, T1, T2]
  }
  trait NodeVConstructor[T <: Ast, T1 <: Ast, T2 <: Ast] {
    def apply(v: T1, p: T2): T
  }

  //

  sealed trait Pattern extends Ast
  trait Pattern_ extends Pattern // trick to inherit sealed trait

  trait Variable[P <: Pattern, N, R] extends Pattern with Leaf {
    def name: N
    def sort: R
    def constructor: VariableConstructor[P, N, R]
  }
  trait VariableConstructor[P <: Pattern, N, R] {
    def apply(name: N, sort: R): P
  }

  trait Application[P <: Pattern, S] extends Pattern with Node[S] {
    def args: Seq[P]
    def constructor: ApplicationConstructor[P, S]
  }
  trait ApplicationConstructor[P <: Pattern, S] {
    def apply(label: S, args: Seq[P]): P
  }

  trait DomainValue[P <: Pattern, S, V] extends Pattern with Node[S] with Leaf {
    def value: V
    def constructor: DomainValueConstructor[P, S, V]
  }
  trait DomainValueConstructor[P <: Pattern, S, V] {
    def apply(label: S, value: V): P
  }

  trait True[P <: Pattern] extends Pattern with Node0[P]
  trait False[P <: Pattern] extends Pattern with Node0[P]
  //
  trait And[P <: Pattern] extends Pattern with Node2[P, P, P]
  trait Or[P <: Pattern] extends Pattern with Node2[P, P, P]
  trait Not[P <: Pattern] extends Pattern with Node1[P, P]
  trait Implies[P <: Pattern] extends Pattern with Node2[P, P, P]
  //
  trait Next[P <: Pattern] extends Pattern with Node1[P, P]
  trait Rewrite[P <: Pattern] extends Pattern with Node2[P, P, P]
  trait Equal[P <: Pattern] extends Pattern with Node2[P, P, P]
  //
  trait Exists[P <: Pattern, V <: Variable[P, N, R], N, R] extends Pattern with NodeV[P, V, P]
  trait ForAll[P <: Pattern, V <: Variable[P, N, R], N, R] extends Pattern with NodeV[P, V, P]

}
