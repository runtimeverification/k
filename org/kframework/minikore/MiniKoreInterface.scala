package org.kframework.minikore

object MiniKoreInterface {

  // abstract types

  sealed trait Ast

  // type for Variable and DomainValue
  trait Leaf extends Ast

  // type for Application and DomainValue
  trait Node extends Ast {
    def label: String
  }

  // types for matching logic connectives

  trait Node0[T <: Pattern] extends Ast {
    def constructor: Node0Constructor[T]
  }
  trait Node0Constructor[T <: Pattern] {
    def apply(): T
  }

  trait Node1[T <: Pattern] extends Ast {
    def p: Pattern
    def constructor: Node1Constructor[T]
  }
  trait Node1Constructor[T <: Pattern] {
    def apply(p: Pattern): T
  }

  trait Node2[T <: Pattern] extends Ast {
    def p: Pattern
    def q: Pattern
    def constructor: Node2Constructor[T]
  }
  trait Node2Constructor[T <: Pattern] {
    def apply(p: Pattern, q: Pattern): T
  }

  trait NodeV[T <: Pattern] extends Ast {
    def v: Variable
    def p: Pattern
    def constructor: NodeVConstructor[T]
  }
  trait NodeVConstructor[T <: Pattern] {
    def apply(v: Variable, p: Pattern): T
  }

  // ground types

  trait Pattern extends Ast

  trait Variable extends Pattern with Leaf {
    def name: String
    def sort: String
    def constructor: VariableConstructor
  }
  trait VariableConstructor {
    def apply(name: String, sort: String): Variable
  }

  trait Application extends Pattern with Node {
    def args: Seq[Pattern]
    def constructor: ApplicationConstructor
  }
  trait ApplicationConstructor {
    def apply(label: String, args: Seq[Pattern]): Application
  }

  trait DomainValue extends Pattern with Node with Leaf {
    def value: String
    def constructor: DomainValueConstructor
  }
  trait DomainValueConstructor {
    def apply(label: String, value: String): DomainValue
  }

  trait True    extends Pattern with Node0[True]
  trait False   extends Pattern with Node0[False]
  trait And     extends Pattern with Node2[And]
  trait Or      extends Pattern with Node2[Or]
  trait Not     extends Pattern with Node1[Not]
  trait Implies extends Pattern with Node2[Implies]
  trait Exists  extends Pattern with NodeV[Exists]
  trait ForAll  extends Pattern with NodeV[ForAll]
  trait Next    extends Pattern with Node1[Next]
  trait Rewrite extends Pattern with Node2[Rewrite]
  trait Equal   extends Pattern with Node2[Equal]


  // factory of constructors

  trait Constructor {
    def Variable    : VariableConstructor
    def Application : ApplicationConstructor
    def DomainValue : DomainValueConstructor
    def True        : Node0Constructor[True]
    def False       : Node0Constructor[False]
    def And         : Node2Constructor[And]
    def Or          : Node2Constructor[Or]
    def Not         : Node1Constructor[Not]
    def Implies     : Node2Constructor[Implies]
    def Exists      : NodeVConstructor[Exists]
    def ForAll      : NodeVConstructor[ForAll]
    def Next        : Node1Constructor[Next]
    def Rewrite     : Node2Constructor[Rewrite]
    def Equal       : Node2Constructor[Equal]
  }

}
