package org.kframework.minikore

import org.kframework.minikore.PatternInterface._


object TreeInterface {


  sealed trait AST[T <: AST[T]]


  sealed trait Node[T <: AST[T]] extends AST[T] with Product {
    def children: Seq[_ <: T]

    def build: NodeBuilder[T]
  }

  object Node {
    def unapply[T <: AST[T]](arg: AST[T]): Option[Seq[_ <: T]] = arg match {
      case n: Node[T] => Some(n.children)
      case _ => None
    }
  }

  trait NodeBuilder[T <: AST[T]] {
    def apply(children: Seq[_ <: T]): T
  }

  trait Node0Builder[T <: AST[T]] extends NodeBuilder[T] {

    def apply(): T

    override def apply(children: Seq[_ <: T]) = {
      assert(children.isEmpty)
      apply()

    }
  }

  trait Node1Builder[T <: AST[T]] extends NodeBuilder[T] {

    def apply(p: T): T

    override def apply(children: Seq[_ <: T]) = {
      assert(children.size == 1)
      apply(children.head)
    }
  }


  trait Node2Builder[T <: AST[T]] extends NodeBuilder[T] {

    def apply(p: T, q: T): T

    override def apply(children: Seq[_ <: T]) = {
      assert(children.size == 2)
      apply(children.head, children(1))
    }
  }


  sealed trait Leaf[T <: AST[T], C] extends AST[T] {
    def contents: C

    def build: LeafBuilder[T, C]
  }

  object Leaf {
    def unapply[T <: AST[T], C](arg: AST[T]): Option[C] = arg match {
      case l: Leaf[T, C] => Some(l.contents)
      case _ => None
    }
  }

  trait LeafBuilder[T <: AST[T], C] {
    def apply(contents: C): T
  }


  trait LabelledNode[L, T <: AST[T]] extends Node[T] {
    def label: L
  }

  trait LabelledNodeBuilder[L, T <: AST[T]] {
    def apply(x: L, c: Seq[_ <: T]): T
  }

  object LabelledNode {
    def unapply[L, T <: AST[T]](arg: AST[T]): Option[(L, Seq[_ <: T])] = arg match {
      case p: LabelledNode[L, T] => Some(p.label, p.children)
      case _ => None
    }
  }


  sealed trait Node0[T <: AST[T]] extends Node[T] {
    override def children = Seq.empty

    def build: Node0Builder[T]

  }

  object Node0 {
    def unapply[T <: AST[T]](arg: AST[T]): Boolean = arg match {
      case p: Node0[T] => true
      case _ => false
    }
  }

  sealed trait Node1[T <: AST[T]] extends Node[T] with Product1[T] {

    def build: NodeBuilder[T]

    override def children = Seq(_1)
  }

  object Node1 {
    def unapply[T <: AST[T]](arg: AST[T]): Option[T] = arg match {
      case n: Node1[T] => Some(n._1)
      case _ => None
    }
  }


  sealed trait Node2[T <: AST[T]] extends Node[T] with Product2[T, T] {

    override def children = Seq(_1, _2)

    def build: Node2Builder[T]

  }

  object Node2 {
    def unapply[T <: AST[T]](arg: AST[T]): Option[(T, T)] = arg match {
      case n: Node2[T] => Some((n._1, n._2))
      case _ => None
    }
  }

}

object PatternInterface {

  import TreeInterface._

  sealed trait Pattern extends AST[Pattern]

  type Sort = String

  trait Variable extends Pattern with Leaf[Pattern, (String, Sort)] {
    def name: String

    def sort: Sort

    override def contents: (String, Sort) = (name, sort)

  }


  trait VariableBuilder extends LeafBuilder[Pattern, (String, Sort)] {

    def apply(name: String, sort: Sort): Variable

    override def apply(contents: (String, Sort)) = apply(contents._1, contents._2)

  }

  object Variable {
    def unapply(arg: Variable): Option[(String, Sort)] = Some(arg.name, arg.sort)
  }

  trait DomainValue extends Pattern with Leaf[Pattern, (String, String)] {
    def label: String

    def value: String


    override def contents = (label, value)
  }

  trait DomainValueBuilder extends LeafBuilder[Pattern, (String, String)] {

    def apply(label: String, value: String): DomainValue

    override def apply(contents: (String, String)): DomainValue = apply(contents._1, contents._2)


  }

  object DomainValue {
    def unapply(arg: Pattern): Option[(String, String)] = arg match {
      case dv: DomainValue => Some(dv.label, dv.value)
      case _ => None
    }
  }

  trait True extends Pattern with Node0[Pattern]

  trait TrueBuilder extends Node0Builder[Pattern] {

    override def apply(): True

  }

  object True {
    def unapply(arg: Pattern): Boolean = arg match {
      case _: True => true
      case _ => false
    }
  }

  trait False extends Pattern with Node0[Pattern]

  trait FalseBuilder extends Node0Builder[Pattern] {

    override def apply(): False

  }

  object False {
    def unapply(arg: Pattern): Boolean = arg match {
      case _: False => true
      case _ => false
    }
  }

  trait And extends Pattern with Node2[Pattern] {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q
  }


  trait AndBuilder extends Node2Builder[Pattern] {

    override def apply(x: Pattern, y: Pattern): And


  }

  object And {
    def unapply(arg: Pattern): Option[(Pattern, Pattern)] = arg match {
      case v: And => Some(v.p, v.q)
      case _ => None
    }
  }

  trait Or extends Pattern with Node2[Pattern] {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q

  }

  trait OrBuilder extends Node2Builder[Pattern] {

    override def apply(x: Pattern, y: Pattern): Or

  }

  object Or {
    def unapply(arg: Pattern): Option[(Pattern, Pattern)] = arg match {
      case v: Or => Some(v.p, v.q)
      case _ => None
    }
  }

  trait Not extends Pattern with Node1[Pattern] {
    def p: Pattern

    override val _1 = p

  }

  trait NotBuilder extends Node1Builder[Pattern] {
    override def apply(p: Pattern): Not

  }

  object Not {
    def unapply(arg: Pattern): Option[Pattern] = arg match {
      case n: Not => Some(n.p)
      case _ => None
    }
  }

  trait Application extends Pattern with LabelledNode[String, Pattern] {

    def args: Seq[_ <: Pattern]

    override def children: Seq[Pattern] = args


  }

  trait ApplicationBuilder extends LabelledNodeBuilder[String, Pattern] {
    override def apply(x: String, c: Seq[_ <: Pattern]): Application
  }

  object Application {
    def unapply(arg: Pattern): Option[(String, Seq[_ <: Pattern])] = arg match {
      case a: Application => Some(a.label, a.args)
      case _ => None
    }
  }

  trait Implies extends Pattern with Node2[Pattern] {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q
  }

  trait ImpliesBuilder extends Node2Builder[Pattern] {
    override def apply(p: Pattern, q: Pattern): Implies
  }

  object Implies {
    def unapply(arg: Pattern): Option[(Pattern, Pattern)] = arg match {
      case v: Implies => Some(v.p, v.q)
      case _ => None
    }
  }

  trait Exists extends Pattern with Node2[Pattern] {
    def v: Variable

    def p: Pattern

    override val _1 = v

    override val _2 = p
  }

  object Exists {
    def unapply(arg: Pattern): Option[(Variable, Pattern)] = arg match {
      case e: Exists => Some(e.v, e.p)
      case _ => None
    }
  }

  trait ExistsBuilder extends Node2Builder[Pattern] {
    override def apply(p: Pattern, q: Pattern): Exists
  }

  trait ForAll extends Pattern with Node2[Pattern] {
    def v: Variable

    def p: Pattern

    override val _1 = v

    override val _2 = p
  }

  trait ForAllBuilder extends Node2Builder[Pattern] {
    override def apply(v: Pattern, p: Pattern): ForAll

  }

  object ForAll {
    def unapply(arg: Pattern): Option[(Variable, Pattern)] = arg match {
      case e: ForAll => Some(e.v, e.p)
      case _ => None
    }
  }

  trait Next extends Pattern with Node1[Pattern] {
    def p: Pattern

    override val _1 = p
  }

  trait NextBuilder extends Node1Builder[Pattern] {

    override def apply(p: Pattern): Next

  }


  object Next {
    def unapply(arg: Pattern): Option[Pattern] = arg match {
      case n: Next => Some(n.p)
      case _ => None
    }
  }

  trait Rewrite extends Pattern with Node2[Pattern] {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q

  }

  trait RewriteBuilder extends Node2Builder[Pattern] {
    def apply(p: Pattern, q: Pattern): Rewrite

  }

  object Rewrite {
    def unapply(arg: Pattern): Option[(Pattern, Pattern)] = arg match {
      case v: Rewrite => Some(v.p, v.q)
      case _ => None
    }
  }

  trait Equals extends Pattern with Node2[Pattern] {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q

  }

  trait EqualsBuilder extends Node2Builder[Pattern] {

    def apply(p: Pattern, q: Pattern): Equals

  }

  object Equals {
    def unapply(arg: Pattern): Option[(Pattern, Pattern)] = arg match {
      case v: Equals => Some(v.p, v.q)
      case _ => None
    }
  }

}

case class Builders(Variable: VariableBuilder,
                    DomainValue: DomainValueBuilder,
                    True: TrueBuilder,
                    False: FalseBuilder,
                    Not: NotBuilder,
                    Next: NextBuilder,
                    Exists: ExistsBuilder,
                    ForAll: ForAllBuilder,
                    And: AndBuilder,
                    Or: OrBuilder,
                    Implies: ImpliesBuilder,
                    Equals: EqualsBuilder,
                    Rewrite: RewriteBuilder,
                    Application: ApplicationBuilder)


