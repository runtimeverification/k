package org.kframework.minikore

import org.kframework.minikore.PatternInterface._


object TreeInterface {


  sealed trait AST


  sealed trait Node extends AST with Product {
    def children: Seq[Pattern]

    def build(children: Seq[Pattern]): Pattern
  }


  object Node {
    def unapply(arg: Node): Option[Seq[Pattern]] = Some(arg.children)
  }


  sealed trait Leaf[C] extends AST {
    def contents: C

    def build(contents: C): Pattern
  }

  object Leaf {
    def unapply[C](arg: AST): Option[C] = arg match {
      case l: Leaf[C] => Some(l.contents)
      case _ => None
    }
  }


  trait LabeledNode[L] extends Node {
    def label: L

    def apply(label: L, children: Seq[Pattern]): Pattern

    override def build(children: Seq[Pattern]) = apply(label, children)
  }

  object LabeledNode {
    def unapply[L](arg: AST): Option[(L, Seq[Pattern])] = arg match {
      case l: LabeledNode[L] => Some(l.label, l.children)
      case _ => None
    }
  }


  sealed trait Node0 extends Node {
    override def children = Seq.empty[Pattern]

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

    override def children = Seq(_1)

    def apply(p: Pattern): Pattern

    override def build(children: Seq[Pattern]) = {
      assert(children.size == 1)
      apply(children.head)
    }
  }

  object Node1 {
    def unapply(arg: Node1): Option[Pattern] = Some(arg._1)
  }


  sealed trait Node2 extends Node with Product2[Pattern, Pattern] {

    override def children = Seq(_1, _2)

    def apply(p: Pattern, q: Pattern): Pattern

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

    override def contents: (String, Sort) = (name, sort)

    def apply(name: String, sort: String): Variable

    override def build(contents: (String, Sort)) = apply(name, sort)
  }


  object Variable {
    def unapply(arg: Variable): Option[(String, Sort)] = Some(arg.name, arg.sort)
  }

  trait DomainValue extends Pattern with Leaf[(String, String)] {
    def label: String

    def value: String

    def apply(label: String, value: String): DomainValue

    override def contents: (String, String) = (label, value)

    override def build(contents: (String, String)) = apply(contents._1, contents._2)
  }


  object DomainValue {
    def unapply(arg: DomainValue): Option[(String, String)] = Some(arg.label, arg.value)
  }

  trait True extends Pattern with Node0 {
    override def apply(): True
  }


  object True {
    def unapply(arg: True): Boolean = true
  }

  trait False extends Pattern with Node0


  object False {
    def unapply(arg: False): Boolean = true
  }

  trait And extends Pattern with Node2 {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q

    override def apply(p: Pattern, q: Pattern): And

  }

  object And {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }


  trait Or extends Pattern with Node2 {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q

    override def apply(p: Pattern, q: Pattern): Or
  }


  object Or {
    def unapply(arg: Or): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }

  trait Not extends Pattern with Node1 {
    def p: Pattern

    override val _1 = p

    override def apply(p: Pattern): Not

  }

  object Not {
    def unapply(arg: Not): Option[Pattern] = Some(arg.p)
  }


  trait Application extends Pattern with LabeledNode[String] {

    def args: Seq[Pattern]

    override def children: Seq[Pattern] = args

    override def apply(label: String, children: Seq[Pattern]): Application

  }


  object Application {
    def unapply(arg: Pattern): Option[(String, Seq[Pattern])] = arg match {
      case a: Application => Some(a.label, a.args)
      case _ => None
    }
  }

  trait Implies extends Pattern with Node2 {

    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q

    override def apply(p: Pattern, q: Pattern): Implies
  }


  object Implies {
    def unapply(arg: Implies): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }

  trait Exists extends Pattern with Node2 {
    def v: Variable

    def p: Pattern

    override val _1 = v

    override val _2 = p

    def apply(v: Variable, p: Pattern): Exists

    override def apply(p: Pattern, q: Pattern): Exists = apply(v, q)
  }

  object Exists {
    def unapply(arg: Exists): Option[(Variable, Pattern)] = Some(arg.v, arg.p)
  }


  trait ForAll extends Pattern with Node2 {
    def v: Variable

    def p: Pattern

    override val _1 = v

    override val _2 = p

    def apply(v: Variable, p: Pattern): ForAll

    override def apply(p: Pattern, q: Pattern): ForAll = apply(p, q)

  }

  object ForAll {
    def unapply(arg: ForAll): Option[(Variable, Pattern)] = Some(arg.v, arg.p)
  }

  trait Next extends Pattern with Node1 {
    def p: Pattern

    override val _1 = p

    override def apply(p: Pattern): Next

  }


  object Next {
    def unapply(arg: Next): Option[Pattern] = Some(arg.p)
  }

  trait Rewrite extends Pattern with Node2 {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q

    override def apply(p: Pattern, q: Pattern): Rewrite
  }


  object Rewrite {
    def unapply(arg: Rewrite): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }

  trait Equals extends Pattern with Node2 {
    def p: Pattern

    def q: Pattern

    override val _1 = p

    override val _2 = q

    override def apply(p: Pattern, q: Pattern): Equals

  }


  object Equals {
    def unapply(arg: Equals): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }

}

object Build {

  trait Builders {

    def Variable(name: String, sort: Sort): Variable

    def DomainValue(label: String, value: String): DomainValue

    def True(): True

    def False(): False

    def Not(p: Pattern): Not

    def Next(p: Pattern): Next

    def And(p: Pattern, q: Pattern): And

    def Or(p: Pattern, q: Pattern): Or

    def Implies(p: Pattern, q: Pattern): Implies

    def Equals(p: Pattern, q: Pattern): Equals

    def Exists(v: Variable, p: Pattern): Exists

    def ForAll(v: Variable, p: Pattern): ForAll

    def Rewrite(p: Pattern, q: Pattern): Rewrite

    def Application(s: String, args: Seq[Pattern]): Application
  }

}

