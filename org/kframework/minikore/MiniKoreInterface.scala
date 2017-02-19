package org.kframework.minikore


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
    def apply(children: Seq[_ <: T]): Node[T]
  }

  trait Node0Builder[T <: AST[T]] extends NodeBuilder[T] with (() => Node[T]) {
    override def apply(children: Seq[_ <: T]) = {
      assert(children.isEmpty)
      apply()

    }
  }

  trait Node1Builder[T <: AST[T]] extends NodeBuilder[T] with ((T) => Node1[T]) {
    override def apply(children: Seq[_ <: T]) = {
      assert(children.size == 1)
      apply(children.head)
    }
  }


  trait Node2Builder[T <: AST[T]] extends NodeBuilder[T] with ((T, T) => Node2[T]) {

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

  trait LeafBuilder[T <: AST[T], C] extends (C => Leaf[T, C]) {
    def apply(contents: C): Leaf[T, C]
  }


  trait LabelBuild[L, T <: AST[T]] extends NodeBuilder[T] with ((Seq[_ <: AST[T]]) => LabelledNode[L, T])

  trait LabelledNode[L, T <: AST[T]] extends Node[T] {

    def label: L

    def build: LabelBuild[L, T]

  }

  trait LabelledNodeBuilder[L, T <: AST[T]] extends ((L, Seq[_ <: AST[T]]) => LabelledNode[L, T])


  sealed trait Node0[T <: AST[T]] extends Node[T] {
    override def children = Seq.empty

    def build: Node0Builder[T]

  }

  sealed trait Node1[T <: AST[T]] extends Node[T] with Product1[T] {

    def build: NodeBuilder[T]

    override def children = Seq(_1)
  }


  sealed trait Node2[T <: AST[T]] extends Node[T] with Product2[T, T] {

    override def children = Seq(_1, _2)

    def build: Node2Builder[T]

  }

}

object PatternInterface {

  import TreeInterface._

  sealed trait Pattern extends AST[Pattern]

  trait Variable extends Pattern with Leaf[Pattern, (String, String)] {
    def name: String

    def sort: String

    override def contents = (name, sort)

  }


  trait VariableBuilder extends LeafBuilder[Pattern, (String, String)] {

    object Variable {
      def unapply(arg: Variable): Option[(String, String)] = Some(arg.name, arg.sort)
    }

  }


  trait DomainValue extends Pattern with Leaf[Pattern, (String, String)] {
    def label: String

    def value: String

    override def contents = (label, value)
  }

  trait DomainValueBuilder extends LeafBuilder[Pattern, (String, String)] {

    object DomainValue {
      def unapply(arg: Pattern): Option[(String, String)] = arg match {
        case dv: DomainValue => Some(dv.label, dv.value)
        case _ => None
      }
    }

  }

  trait True extends Pattern with Node0[Pattern]

  trait TrueBuilder extends Node0Builder[Pattern] {

    object True {
      def unapply(arg: Pattern): Boolean = arg match {
        case t: True => true
        case _ => false
      }
    }

  }


  trait False extends Pattern with Node0[Pattern]

  trait FalseBuilder extends Node0Builder[Pattern] {

    object False {
      def unapply(arg: Pattern): Boolean = arg match {
        case t: False => true
        case _ => false
      }
    }

  }

  trait And extends Pattern with Node2[Pattern] {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q
  }


  trait AndBuilder extends Node2Builder[Pattern] {

    object And {
      def unapply(arg: Pattern): Option[(Pattern, Pattern)] = arg match {
        case v: And => Some(v.p, v.q)
        case _ => None
      }
    }

  }

  trait Or extends Pattern with Node2[Pattern] {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q

  }

  trait OrBuilder extends Node2Builder[Pattern] {

    object Or {
      def unapply(arg: Pattern): Option[(Pattern, Pattern)] = arg match {
        case v: Or => Some(v.p, v.q)
        case _ => None
      }
    }

  }

  trait Not extends Pattern with Node1[Pattern] {
    def p: Pattern

    override val _1 = p

  }

  trait NotBuilder extends Node1Builder[Pattern] {

    object Not {
      def unapply(arg: Pattern): Option[Pattern] = arg match {
        case n: Not => Some(n.p)
        case _ => None
      }
    }

  }

  trait Application extends Pattern with LabelledNode[String, Pattern] {

    def args: Seq[Pattern]

    override def children: Seq[Pattern] = args


  }

  trait ApplicationBuilder extends LabelledNodeBuilder[String, Pattern] {

    object Application {
      def unapply(arg: Pattern): Option[(String, Seq[Pattern])] = arg match {
        case a: Application => Some(a.label, a.args)
        case _ => None
      }
    }

  }


  trait Implies extends Pattern with Node2[Pattern] {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q
  }

  trait ImpliesBuilder extends Node2Builder[Pattern] {

    object Implies {
      def unapply(arg: Pattern): Option[(Pattern, Pattern)] = arg match {
        case v: Implies => Some(v.p, v.q)
        case _ => None
      }
    }

  }


  trait Exists extends Pattern with Node2[Pattern] {
    def v: Variable

    def p: Pattern

    override val _1 = v

    override val _2 = p
  }

  trait ExistsBuilder extends Node2Builder[Pattern] {

    object Exists {
      def unapply(arg: Pattern): Option[(Variable, Pattern)] = arg match {
        case e: Exists => Some(e.v, e.p)
        case _ => None
      }
    }

  }

  trait ForAll extends Pattern with Node2[Pattern] {
    def v: Variable

    def p: Pattern

    override val _1 = v

    override val _2 = p
  }

  trait ForAllBuilder extends Node2Builder[Pattern] {

    object ForAll {
      def unapply(arg: Pattern): Option[(Variable, Pattern)] = arg match {
        case e: ForAll => Some(e.v, e.p)
        case _ => None
      }
    }

  }

  trait Next extends Pattern with Node1[Pattern] {
    def p: Pattern

    override val _1 = p
  }

  trait NextBuilder extends Node1Builder[Pattern] {

    object Next {
      def unapply(arg: Pattern): Option[Pattern] = arg match {
        case n: Next => Some(n.p)
        case _ => None
      }
    }

  }


  trait Rewrite extends Pattern with Node2[Pattern] {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q

  }

  trait RewriteBuilder extends Node2Builder[Pattern] {

    object Rewrite {
      def unapply(arg: Pattern): Option[(Pattern, Pattern)] = arg match {
        case v: Rewrite => Some(v.p, v.q)
        case _ => None
      }
    }

  }


  trait Equals extends Pattern with Node2[Pattern] {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q

  }

  trait EqualsBuilder extends Node2Builder[Pattern] {

    object Equals {
      def unapply(arg: Pattern): Option[(Pattern, Pattern)] = arg match {
        case v: Equals => Some(v.p, v.q)
        case _ => None
      }
    }

  }


}


