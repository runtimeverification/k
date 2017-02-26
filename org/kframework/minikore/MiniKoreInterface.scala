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


  sealed trait Leaf[C] extends AST with Product1[C] {
    def build(_1: C): Pattern
  }


  object Leaf {
    def unapply(arg: AST): Option[_] = arg match {
      case l: Leaf[_] => Some(l._1)
      case _ => None
    }
  }


  trait LabeledNode[L] extends Node {
    def label: L

    def apply(label: L, children: Seq[Pattern]): Pattern

    override def build(children: Seq[Pattern]) = apply(label, children)
  }


  object LabeledNode {
    def unapply[_](arg: AST): Option[(_, Seq[Pattern])] = arg match {
      case l: LabeledNode[_] => Some(l.label, l.args)
      case _ => None
    }
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
    def unapply(arg: AST): Boolean = arg match {
      case _: Node0 => true
      case _ => false
    }
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


  type Sort = String


  trait Variable extends Pattern with Leaf[(String, Sort)] {
    def name: String

    def sort: Sort

    override val _1: (String, Sort) = (name, sort)

    def apply(name: String, sort: String): Variable

    override def build(contents: (String, Sort)) = apply(contents._1, contents._2)
  }


  object Variable {
    def unapply(arg: Variable): Option[(String, Sort)] = Some(arg.name, arg.sort)
  }


  trait DomainValue extends Pattern with Leaf[(String, String)] {
    def label: String

    def value: String

    def apply(label: String, value: String): DomainValue

    override val _1: (String, String) = (label, value)

    override def build(contents: (String, String)) = apply(contents._1, contents._2)
  }


  object DomainValue {
    def unapply(arg: DomainValue): Option[(String, String)] = Some(arg.label, arg.value)
  }


  trait Top extends Pattern with Node0 {
    override def apply(): Top
  }


  object Top {
    def unapply(arg: Top): Boolean = true
  }


  trait Bottom extends Pattern with Node0


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


  trait Application extends Pattern with LabeledNode[String] {
    override def apply(label: String, args: Seq[Pattern]): Application
  }


  object Application {
    def unapply(arg: Pattern): Option[(String, Seq[Pattern])] = arg match {
      case a: Application => Some(a.label, a.args)
      case _ => None
    }
  }


  trait Implies extends Pattern with Node2 {
    override def apply(_1: Pattern, _2: Pattern): Implies
  }


  object Implies {
    def unapply(arg: Implies): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  trait Exists extends Pattern with Node2 {
    override val _1: Variable

    def apply(_1: Variable, _2: Pattern): Exists

    override def apply(_1: Pattern, _2: Pattern): Exists = apply(_1.asInstanceOf[Variable], _2)
  }


  object Exists {
    def unapply(arg: Exists): Option[(Variable, Pattern)] = Some(arg._1, arg._2)
  }


  trait ForAll extends Pattern with Node2 {
    override val _1: Variable

    def apply(_1: Variable, _2: Pattern): ForAll

    override def apply(_1: Pattern, _2: Pattern): ForAll = apply(_1.asInstanceOf[Variable], _2)
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

    def Variable(name: String, sort: Sort): Variable

    def DomainValue(label: String, value: String): DomainValue

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

    def Application(s: String, args: Seq[Pattern]): Application
  }

}

