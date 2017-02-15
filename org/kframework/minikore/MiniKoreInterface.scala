package org.kframework.minikore


object TreeInterface {

  sealed trait AST

  sealed trait Node[T] extends AST {
    def children: Seq[AST]

    def build: NodeBuilder[T]
  }

  trait NodeBuilder[T] extends (Seq[_ <: AST] => Node[T])

  trait Node0Builder[T] extends NodeBuilder[T] with (() => Node[T]) {
    override def apply(children: Seq[_ <: AST]) = {
      assert(children.isEmpty)
      apply()
    }
  }

  trait Node1Builder[P <: AST, T] extends NodeBuilder[T] with ((P) => Node1[P, T]) {

    def apply(p: P): Node1[P, T]

    override def apply(children: Seq[_ <: AST]) = {
      assert(children.size == 1)
      apply(children.head.asInstanceOf[P])
    }
  }

  trait Node2Builder[P1 <: AST, P2 <: AST, T] extends NodeBuilder[T] with ((P1, P2) => Node2[P1, P2, T]) {


    override def apply(children: Seq[_ <: AST]) = {
      assert(children.size == 2)
      apply(children.head.asInstanceOf[P1], children(1).asInstanceOf[P2])
    }
  }

  trait Node2BinderBuilder[P1 <: AST, P2 <: AST, T] extends NodeBuilder[T] with ((P1, P2) => Node2Binder[P1, P2, T]) {


    override def apply(children: Seq[_ <: AST]) = {
      assert(children.size == 2)
      apply(children.head.asInstanceOf[P1], children(1).asInstanceOf[P2])
    }
  }


  trait LabelledNodeBuilder[L, T] extends NodeBuilder[T] with ((Seq[_ <: AST]) => LabelledNode[L, T])


  sealed trait Leaf[C] extends AST {
    def contents: C

    def build: LeafBuilder[C]
  }

  trait LeafBuilder[C] extends (C => Leaf[C]) {
    def apply(contents: C): Leaf[C]
  }

  sealed trait LabelledNode[L, T] extends Node[T] {
    def label: L

    def args: Seq[_ <: AST]

    def build: LabelledNodeBuilder[L, T]
  }

  sealed trait Node0[T] extends Node[T] {
    override def children = Seq.empty

    def build: Node0Builder[T]

  }

  sealed trait Node1[P <: AST, T] extends Node[T] {
    def p: P

    def build: Node1Builder[P, T]

    override def children = Seq(p)
  }


  sealed trait Node2[P1 <: AST, P2 <: AST, T] extends Node[T] {
    def p: P1

    def q: P2

    override def children = Seq(p, q)

    def build: Node2BinderBuilder[P1, P2, T]

  }

  sealed trait Node2Binder[P1 <: AST, P2 <: AST, T] extends Node[T] {
    def v: P1

    def p: P2

    override def children = Seq(v, p)

    def build: Node2BinderBuilder[P1, P2, T]

  }

}

object PatternInterface {

  import org.kframework.minikore.TreeInterface._

  sealed trait Pattern extends AST

  trait Variable extends Pattern with Leaf[(String, String)] {
    def name: String

    def sort: String

    override def contents = (name, sort)

  }

  object Variable {
    def unapply(arg: Variable): Option[(String, String)] = Some(arg.name, arg.sort)
  }

  trait DomainValue extends Pattern with Leaf[(String, String)] {
    def label: String

    def value: String

    override def contents = (label, value)
  }

  object DomainValue {
    def unapply(arg: DomainValue): Option[(String, String)] = Some(arg.label, arg.value)
  }

  trait True extends Pattern with Node0[True]

  object True {
    def unapply(arg: True): Boolean = true
  }


  trait False extends Pattern with Node0[False]

  object False

  trait And extends Pattern with Node2[Pattern, Pattern, And]


  object And {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }


  trait Or extends Pattern with Node2[Pattern, Pattern, Or]

  object Or {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }

  trait Not extends Pattern with Node1[Pattern, Not]

  object Not {
    def unapply(arg: Not): Option[Pattern] = Some(arg.p)
  }

  trait Application extends Pattern with LabelledNode[String, Application] {
    def label: String

    def args: Seq[Pattern]

    override def children: Seq[Pattern] = args

  }

  object Application {
    def unapply(arg: Application): Option[(String, Seq[Pattern])] = Some(arg.label, arg.args)
  }

  trait Implies extends Pattern with Node2[Pattern, Pattern, Implies]


  object Implies {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }

  trait Exists extends Pattern with Node2Binder[Variable, Pattern, Exists]

  object Exists {
    def unapply(arg: Exists): Option[(Variable, Pattern)] = Some(arg.v, arg.p)
  }

  trait ForAll extends Pattern with Node2Binder[Variable, Pattern, ForAll]

  object ForAll {
    def unapply(arg: Exists): Option[(Variable, Pattern)] = Some(arg.v, arg.p)
  }

  trait Next extends Pattern with Node1[Pattern, Next]


  object Next {
    def unapply(arg: Not): Option[Pattern] = Some(arg.p)
  }

  trait Rewrite extends Pattern with Node2[Pattern, Pattern, Rewrite]

  object Rewrite {
    def unapply(arg: Rewrite): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }

  trait Equals extends Pattern with Node2[Pattern, Pattern, Equals]

  object Equals {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }


}

trait FactoryInterface {

  import org.kframework.minikore.PatternInterface._

  def Application(label: String, args: Seq[Pattern]): Application

  def Variable(name: String, sort: String): Variable

  def DomainValue(label: String, value: String): DomainValue

  def True(): True

  def False(): False

  def And(p: Pattern, q: Pattern): And

  def Or(p: Pattern, q: Pattern): Or

  def Not(p: Pattern): Not

  def Implies(p: Pattern, q: Pattern): Implies

  def Exists(v: Variable, p: Pattern): Exists

  def ForAll(v: Variable, p: Pattern): ForAll

  def Next(p: Pattern): Next

  def Rewrite(p: Pattern, q: Pattern): Rewrite

  def Equals(p: Pattern, q: Pattern): Equals
}
