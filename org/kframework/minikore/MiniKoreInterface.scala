package org.kframework.minikore

import org.kframework.minikore.PatternInterface._


object TreeInterface {

  sealed trait AST


  sealed trait Node extends AST with Product {
    def args: Seq[Pattern]

    def build(children: Seq[Pattern]): Pattern
  }


  object Node {
    def unapply(arg: Node): Option[Seq[Pattern]] = Some(arg.args)
  }


  sealed trait Leaf[C] extends AST with Product {
    def contents: C

    def build(contents: C): Pattern
  }

  object Leaf {
    def unapply(arg: Leaf[_]): Option[_] = Some(arg.contents)
  }

  sealed trait Leaf2[CC1, CC2] extends Leaf[Product2[CC1, CC2]] with Product2[CC1, CC2] {
    override def contents: Product2[CC1, CC2] = (_1, _2)

    def apply(_1: CC1, _2: CC2): Pattern

    override def build(contents: Product2[CC1, CC2]): Pattern = apply(contents._1, contents._2)
  }

  object Leaf2 {
    def unapply(arg: Leaf2[_, _]): Option[(_, _)] = Some(arg._1, arg._2)
  }

  trait LabeledNode[L] extends Node with Product1[L] {
    override val _1: L

    def apply(_1: L, args: Seq[Pattern]): Pattern

    override def build(args: Seq[Pattern]): Pattern = apply(_1, args)
  }

  object LabeledNode {
    def unapply(arg: LabeledNode[_]): Option[(_, Seq[Pattern])] = Some(arg._1, arg.args)
  }

  sealed trait Node0 extends Node {
    override def args = Seq.empty[Pattern]

    def apply(): Pattern

    override def build(children: Seq[Pattern]) = {
      assert(children.isEmpty)
      apply()
    }
  }


  object Node0 {
    def unapply(arg: Node0): Boolean = true
  }


  sealed trait Node1 extends Node with Product1[Pattern] {

    override def args = Seq(_1)

    def apply(_1: Pattern): Pattern

    override def build(children: Seq[Pattern]) = {
      assert(children.size == 1)
      apply(children.head)
    }
  }

  object Node1 {
    def unapply(arg: Node1): Option[Pattern] = Some(arg._1)
  }

  sealed trait BinderNode extends Node with Product2[Variable, Pattern] {
    def apply(_1: Variable, _2: Pattern): Pattern

    override def args = Seq(_1, _2)

    override def build(children: Seq[Pattern]): Pattern = {
      assert(children.size == 2)
      apply(children.head.asInstanceOf[Variable], children(1))
    }
  }

  object BinderNode {
    def unapply(arg: BinderNode): Option[(Variable, Pattern)] = Some(arg._1, arg._2)
  }


  sealed trait Node2 extends Node with Product2[Pattern, Pattern] {

    def apply(_1: Pattern, _2: Pattern): Pattern

    override def args = Seq(_1, _2)

    override def build(children: Seq[Pattern]) = {
      assert(children.size == 2)
      apply(children.head, children(1))
    }
  }


  object Node2 {
    def unapply(arg: Node2): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }

}

object PatternInterface {

  import TreeInterface._


  sealed trait Pattern extends AST

  type Name = String

  type Sort = String


  trait Variable extends Pattern with Leaf2[Name, Sort] {
    def apply(_1: Name, _2: Sort): Variable

  }


  object Variable {
    def unapply(arg: Variable): Option[(Name, Sort)] = Some(arg._1, arg._2)
  }

  type Label = String

  type Value = String


  trait DomainValue extends Pattern with Leaf2[Label, Value] {
    def apply(_1: Label, _2: Value): DomainValue
  }


  object DomainValue {
    def unapply(arg: DomainValue): Option[(Label, Value)] = Some(arg._1, arg._2)
  }


  trait Top extends Pattern with Node0 {
    override def apply(): Top
  }


  object Top {
    def unapply(arg: Top): Boolean = true
  }


  trait Bottom extends Pattern with Node0 {
    override def apply(): Bottom
  }


  object Bottom {
    def unapply(arg: Bottom): Boolean = true
  }

  trait And extends Pattern with Node2 {
    override def apply(_1: Pattern, _2: Pattern): And
  }


  object And {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  trait Or extends Pattern with Node2 {
    override def apply(_1: Pattern, _2: Pattern): Or
  }


  object Or {
    def unapply(arg: Or): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  trait Not extends Pattern with Node1 {
    override def apply(_1: Pattern): Not
  }


  object Not {
    def unapply(arg: Not): Option[Pattern] = Some(arg._1)
  }


  trait Application extends Pattern with LabeledNode[Label] {
    override def apply(_1: Label, args: Seq[Pattern]): Application
  }


  object Application {
    def unapply(arg: Application): Option[(Label, Seq[Pattern])] = Some(arg._1, arg.args)
  }


  trait Implies extends Pattern with Node2 {
    override def apply(_1: Pattern, _2: Pattern): Implies
  }


  object Implies {
    def unapply(arg: Implies): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  trait Exists extends Pattern with BinderNode {
    def apply(_1: Variable, _2: Pattern): Exists
  }


  object Exists {
    def unapply(arg: Exists): Option[(Variable, Pattern)] = Some(arg._1, arg._2)
  }


  trait ForAll extends Pattern with BinderNode {
    def apply(_1: Variable, _2: Pattern): ForAll
  }


  object ForAll {
    def unapply(arg: ForAll): Option[(Variable, Pattern)] = Some(arg._1, arg._2)
  }


  trait Next extends Pattern with Node1 {
    override def apply(_1: Pattern): Next
  }


  object Next {
    def unapply(arg: Next): Option[Pattern] = Some(arg._1)
  }


  trait Rewrite extends Pattern with Node2 {
    override def apply(_1: Pattern, _2: Pattern): Rewrite
  }


  object Rewrite {
    def unapply(arg: Rewrite): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  trait Equals extends Pattern with Node2 {
    override def apply(_1: Pattern, _2: Pattern): Equals
  }


  object Equals {
    def unapply(arg: Equals): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }

}

object Build {

  trait Builders {

    def Variable(_1: Name, _2: Sort): Variable

    def DomainValue(_1: Label, _2: Sort): DomainValue

    def Top(): Top

    def Bottom(): Bottom

    def Not(_1: Pattern): Not

    def Next(_1: Pattern): Next

    def And(_1: Pattern, _2: Pattern): And

    def Or(_1: Pattern, _2: Pattern): Or

    def Implies(_1: Pattern, _2: Pattern): Implies

    def Equals(_1: Pattern, _2: Pattern): Equals

    def Exists(_1: Variable, _2: Pattern): Exists

    def ForAll(_1: Variable, _2: Pattern): ForAll

    def Rewrite(_1: Pattern, _2: Pattern): Rewrite

    def Application(_1: Label, args: Seq[Pattern]): Application
  }

}

