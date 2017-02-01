package org.kframework.minikore

object MiniKoreInterface {

  // View & Constructor

  trait Ast

  trait LeafConstructor[T <: Ast, V] extends Ast {
    def constructor: V => T
  }

  trait Leaf[T <: Ast, V] extends Ast with LeafConstructor[T, V]

  trait Node0Constructor[T <: Ast] extends Ast {
    def constructor: () => T
  }

  trait Node0[T <: Ast] extends Ast with Node0Constructor[T]

  trait Node1Constructor[T <: Ast, T1 <: Ast] extends Ast {
    def constructor: T1 => T
  }

  trait Node1[T <: Ast, T1 <: Ast] extends Ast with Node1Constructor[T, T1] {
    def p: T1
  }

  trait Node2Constructor[T <: Ast, T1 <: Ast, T2 <: Ast] extends Ast {
    def constructor: (T1, T2) => T
  }

  trait Node2[T <: Ast, T1 <: Ast, T2 <: Ast] extends Ast with Node2Constructor[T, T1, T2] {
    def p: T1
    def q: T2
  }

  trait NodeSeqConstructor[T <: Ast, V, T1 <: Ast] extends Ast {
    def constructor: (V, Seq[T1]) => T
  }

  trait NodeSeq[T <: Ast, V, T1 <: Ast] extends Ast with NodeSeqConstructor[T, V, T1] {
    def args: Seq[T1]
  }

  // Interface

  trait Pattern extends Ast

  trait Variable[P <: Pattern] extends Pattern with Leaf[P, (String, String)] {
    def name: String
    def sort: String
  }

  trait Application[P <: Pattern] extends Pattern with NodeSeq[P, String, P] {
    def label: String
  }

  trait DomainValue[P <: Pattern] extends Pattern with Leaf[P, (String, String)] {
    def label: String
    def value: String
  }

  trait True[P <: Pattern] extends Pattern with Node0[P]
  trait False[P <: Pattern] extends Pattern with Node0[P]

  trait And[P <: Pattern] extends Pattern with Node2[P, P, P]
  trait Or[P <: Pattern] extends Pattern with Node2[P, P, P]
  trait Not[P <: Pattern] extends Pattern with Node1[P, P]
  trait Implies[P <: Pattern] extends Pattern with Node2[P, P, P]

  trait Binder[V <: Variable[P], P <: Pattern] extends Pattern with Node2Constructor[P, V, P]{
    def v: V
    def p: P
  }
  trait Exists[V <: Variable[P], P <: Pattern] extends Pattern with Binder[V, P]
  trait ForAll[V <: Variable[P], P <: Pattern] extends Pattern with Binder[V, P]

  trait Next[P <: Pattern] extends Pattern with Node1[P, P]
  trait Rewrite[P <: Pattern] extends Pattern with Node2[P, P, P]
  trait Equal[P <: Pattern] extends Pattern with Node2[P, P, P]

}
