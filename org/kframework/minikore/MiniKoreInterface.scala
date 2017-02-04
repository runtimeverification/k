package org.kframework.minikore


object TreeInterface {

  import org.kframework.minikore.PatternInterface.Pattern

  trait AST

  // T - Type of Pattern, C - Type of Children, A - Constructor's Arguments
  sealed trait Node[T, C, CT] extends AST {
    def construct: Any => T

    def children: C

    def childrenAsSeq: Seq[Pattern]
  }

  object Node {
    def unapply(arg: Node[_, _, _]): Option[_] = {
      arg.children match {
        case None => None
        case x@_ => Some(x)
      }
    }
  }

  // A Pattern Such as True/False takes no arguments, hence types of Children is None, Constructor's arguments is None.
  sealed trait Node0[T] extends Node[T, None.type, () => T] {
    override def children = None

    override def childrenAsSeq = Seq.empty[Pattern]
  }

  // A Pattern such as Not, takes 1 argument, and the type of the children is the same.
  sealed trait Node1[T, C <: Pattern] extends Node[T, C, C => T]

  object Node1 {
    def unapply(arg: Node1[_, _]): Option[_] = Some(arg.children)
  }


  sealed trait Node2[T, C1 <: Pattern, C2 <: Pattern] extends Node[T, (C1, C2), (C1, C2) => T]

  object Node2 {
    def unapply(arg: Node2[_, _, _]): Option[_] = Some(arg.children)
  }


  // An Application Node takes a Label Type, and a Children type. The type of the constructor is a composite type.
  sealed trait NodeApply[T, Label, Children] extends Node[T, Children, (Label, Children) => T]

  object NodeApply {
    def unapply(arg: NodeApply[_, _, _]): Option[_] = Some(arg.children)
  }

  sealed trait Leaf[T <: Pattern, Construct] extends AST {
    def construct: Construct
  }

}

object PatternInterface {

  import org.kframework.minikore.TreeInterface._

  trait Pattern

  trait Variable extends Pattern with Leaf[Variable, (String, String) => Variable] {
    def name: String

    def sort: String
  }

  object Variable {
    def unapply(arg: Variable): Option[(String, String)] = Some(arg.name, arg.sort)
  }

  trait DomainValue extends Pattern with Leaf[DomainValue, (String, String) => DomainValue] {
    def label: String

    def value: String
  }

  object DomainValue {
    def unapply(arg: DomainValue): Option[(String, String)] = Some(arg.label, arg.value)
  }

  trait True extends Pattern with Node0[True]

  object True {
    def unapply(arg: True): Boolean = true
  }


  trait False extends Pattern with Node0[False]

  object False {
    def unapply(arg: False): Boolean = false
  }

  trait And extends Pattern with Node2[And, Pattern, Pattern] {
    def p: Pattern

    def q: Pattern

    override def children: (Pattern, Pattern) = (p, q)

    override def childrenAsSeq: Seq[Pattern] = Seq(p, q)

  }

  object And {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }


  trait Or extends Pattern with Node2[Or, Pattern, Pattern] {
    def p: Pattern

    def q: Pattern

    override def children: (Pattern, Pattern) = (p, q)

    override def childrenAsSeq: Seq[Pattern] = Seq(p, q)
  }

  object Or {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }

  trait Not extends Pattern with Node1[Not, Pattern] {
    def p: Pattern

    override def children: Pattern = p

    override def childrenAsSeq: Seq[Pattern] = Seq(p)

  }

  object Not {
    def unapply(arg: Not): Option[Pattern] = Some(arg.p)
  }

  trait Application extends Pattern with NodeApply[Application, String, Seq[Pattern]] {
    def label: String

    def args: Seq[Pattern]

    override def children: Seq[Pattern] = args

    override def childrenAsSeq: Seq[Pattern] = args
  }

  object Application {
    def unapply(arg: Application): Option[(String, Seq[Pattern])] = Some(arg.label, arg.args)
  }

  trait Implies extends Pattern with Node2[Implies, Pattern, Pattern] {

    def p: Pattern

    def q: Pattern

    override def children: (Pattern, Pattern) = (p, q)

    override def childrenAsSeq: Seq[Pattern] = Seq(p, q)
  }

  object Implies {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }

  trait Exists extends Pattern with Node2[Exists, Variable, Pattern] {
    def v: Variable

    def p: Pattern

    override def children: (Variable, Pattern) = (v, p)

    override def childrenAsSeq: Seq[Pattern] = Seq(v, p)
  }

  object Exists {
    def unapply(arg: Exists): Option[(Variable, Pattern)] = Some(arg.v, arg.p)
  }

  trait ForAll extends Pattern with Node2[ForAll, Variable, Pattern] {
    def v: Variable

    def p: Pattern

    override def children: (Variable, Pattern) = (v, p)

    override def childrenAsSeq: Seq[Pattern] = Seq(v, p)
  }

  object ForAll {
    def unapply(arg: Exists): Option[(Variable, Pattern)] = Some(arg.v, arg.p)
  }

  trait Next extends Pattern with Node1[Next, Pattern] {

    def p: Pattern

    override def children: Pattern = p

    override def childrenAsSeq: Seq[Pattern] = Seq(p)
  }

  object Next {
    def unapply(arg: Not): Option[Pattern] = Some(arg.p)
  }

  trait Rewrite extends Pattern with Node2[Rewrite, Pattern, Pattern] {
    def p: Pattern

    def q: Pattern

    override def children: (Pattern, Pattern) = (p, q)

    override def childrenAsSeq: Seq[Pattern] = Seq(p, q)
  }

  object Rewrite {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some(arg.p, arg.q)
  }

  trait Equals extends Pattern with Node2[Equals, Pattern, Pattern] {
    def p: Pattern

    def q: Pattern

    override def children: (Pattern, Pattern) = (p, q)

    override def childrenAsSeq: Seq[Pattern] = Seq(p, q)
  }

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
