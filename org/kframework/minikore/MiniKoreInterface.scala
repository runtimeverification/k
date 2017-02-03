package org.kframework.minikore

object MiniKoreInterface {

  trait Pattern

  trait AST

  // T - Type of Pattern, C - Type of Children, A - Constructor's Arguments
  sealed trait Node[T <: Pattern, C, A] extends AST {
    def apply: A => T

    def children: C

    def childrenAsSeq: Seq[Pattern]
  }

  // A Pattern Such as True/False takes no arguments, hence types of Children is None, Constructor's arguments is None.
  sealed trait Node0[T] extends Node[T, None.type, None.type] {
    override def children = None

    override def childrenAsSeq = Seq.empty[Pattern]
  }

  // A Pattern such as Not, takes 1 argument, and the type of the children is the same.
  sealed trait Node1[T, C <: Pattern] extends Node[T, C, C]


  sealed trait Node2[T, C1 <: Pattern, C2 <: Pattern] extends Node[T, (C1, C2), (C1, C2)]


  // An Application Node takes a Label Type, and a Children type. The type of the constructor is a composite type.
  sealed trait NodeApply[T, Label, Children] extends Node[T, Children, (Label, Children)]

  sealed trait Leaf[T <: Pattern, A] extends AST {
    def apply: A => T
  }

  trait Variable extends Pattern with Leaf[Variable, (String, String)]

  trait DomainValue extends Pattern with Leaf[DomainValue, (String, String)]

  trait True extends Pattern with Node0[True]

  trait False extends Pattern with Node0[False]

  trait And extends Pattern with Node2[And, Pattern, Pattern]

  trait Or extends Pattern with Node2[Or, Pattern, Pattern]

  trait Not extends Pattern with Node1[Not, Pattern]

  trait Application extends Pattern with NodeApply[Application, String, Seq[Pattern]]

  trait Implies extends Pattern with Node2[Implies, Pattern, Pattern]

  trait Exists extends Pattern with Node2[Exists, Variable, Pattern]

  trait ForAll extends Pattern with Node2[ForAll, Variable, Pattern]

  trait Next extends Pattern with Node1[Next, Pattern]

  trait Rewrite extends Pattern with Node2[Rewrite, Pattern, Pattern]

  trait Equals extends Pattern with Node2[Equals, Pattern, Pattern]

}
