package org.kframework.minikore.interfaces

object tree {

  import pattern._

  /**
    * Base type of the Tree interface. [[Pattern]] extends AST.
    */
  sealed trait AST

  /**
    * Specifies Node behavior of [[Pattern]].
    *
    * Allows matching a Pattern against as a Node,
    * and building a Pattern from a list of Patterns.
    */
  sealed trait Node extends AST with Product {
    def args: Seq[Pattern]

    /* Allows building Nodes using a list of Patterns */
    def build(children: Seq[Pattern]): Pattern
  }

  object Node {
    def unapply(arg: Node): Option[Seq[Pattern]] = Some(arg.args)
  }

  /**
    * Specifies Leaf Behavior of Patterns.
    * @tparam C The Contents of the Leaf.
    */
  sealed trait Leaf[C] extends AST with Product {
    def contents: C

    /* Allows building a leaf using its contents */
    def build(contents: C): Pattern
  }

  object Leaf {
    def unapply[C](arg: Leaf[C]): Option[C] = Some(arg.contents)
  }

  /**
    * A Leaf with only two fields as its contents. [[DomainValue]], [[Variable]] extend this trait.
    * @tparam CC1 Type of First Field.
    * @tparam CC2 Type of Second Field.
    */
  sealed trait Leaf2[CC1, CC2] extends Leaf[Product2[CC1, CC2]] with Product2[CC1, CC2] {
    override def contents: Product2[CC1, CC2] = (_1, _2)

    def apply(_1: CC1, _2: CC2): Pattern

    override def build(contents: Product2[CC1, CC2]): Pattern = apply(contents._1, contents._2)
  }

  object Leaf2 {
    def unapply[CC1, CC2](arg: Leaf2[CC1, CC2]): Option[(CC1, CC2)] = Some(arg._1, arg._2)
  }


  /**
    * Node that has a Label. [[Application]] that extends this trait.
    * @tparam L Type of Label.
    */
  sealed trait LabeledNode[L] extends Node with Product1[L] {
    def apply(_1: L, args: Seq[Pattern]): Pattern

    override def build(children: Seq[Pattern]): Pattern = apply(_1, children)
  }

  object LabeledNode {
    def unapply[L](arg: LabeledNode[L]): Option[(L, Seq[Pattern])] = Some(arg._1, arg.args)
  }


  /**
    * A Node with empty list of Patterns as its args list. [[Top]], [[Bottom]] extend this trait.
    */
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

  /**
    * A Node with a single pattern in its args list. Extended by [[Next]], [[Not]].
    */
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

  /**
    * A Node with 2 Patterns in its args list. Extended by [[Or]], [[And]], [[Implies]], [[Equals]], [[Rewrite]].
    */
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


  /**
    * Extends [[Node2]], and only allows [[Variable]] as the first element in its args list. Extended bu [[Exists]], [[ForAll]].
    */
  sealed trait BinderNode extends Node2 {
    def apply(_1: Variable, _2: Pattern): Pattern

    override val _1: Variable

    override def apply(_1: Pattern, _2: Pattern) = apply(_1.asInstanceOf[Variable], _2)

    override def build(children: Seq[Pattern]): Pattern = {
      assert(children.size == 2)
      apply(children.head.asInstanceOf[Variable], children(1))
    }
  }

  object BinderNode {
    def unapply(arg: BinderNode): Option[(Variable, Pattern)] = Some(arg._1, arg._2)
  }

}


object pattern {

  import tree._

  /* ML Pattern Type */
  sealed trait Pattern extends AST

  type Name = String

  type Sort = String

  /**
    * Matching Logic Variable.
    * Needs 2 strings - representing name and sort respectively to construct.
    */
  trait Variable extends Pattern with Leaf2[Name, Sort] {
    def apply(_1: Name, _2: Sort): Variable
  }

  object Variable {
    def unapply(arg: Variable): Option[(Name, Sort)] = Some(arg._1, arg._2)
  }


  type Label = String

  type Value = String

  /**
    * Matching Logic Domain Value.
    * Needs 2 strings - representing the label, and the value to construct.
    */
  trait DomainValue extends Pattern with Leaf2[Label, Value] {
    def apply(_1: Label, _2: Value): DomainValue
  }

  object DomainValue {
    def unapply(arg: DomainValue): Option[(Label, Value)] = Some(arg._1, arg._2)
  }

  /**
    * Matching Logic Top. Requires no parameters.
    */
  trait Top extends Pattern with Node0 {
    override def apply(): Top
  }

  object Top {
    def unapply(arg: Top): Boolean = true
  }

  /**
    * Matching Logic Bottom. Requires no parameters.
    */
  trait Bottom extends Pattern with Node0 {
    override def apply(): Bottom
  }

  object Bottom {
    def unapply(arg: Bottom): Boolean = true
  }


  /**
    * Matching Logic And. Requires two [[Pattern]], represented as _1, and _2.
    */
  trait And extends Pattern with Node2 {
    override def apply(_1: Pattern, _2: Pattern): And
  }

  object And {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  /**
    * Matching Logic Or. Requires two [[Pattern]], represented as _1, and _2.
    */
  trait Or extends Pattern with Node2 {
    override def apply(_1: Pattern, _2: Pattern): Or
  }

  object Or {
    def unapply(arg: Or): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  /**
    * Matching Logic Not. Requies one [[Pattern]], represented as _1.
    */
  trait Not extends Pattern with Node1 {
    override def apply(_1: Pattern): Not
  }

  object Not {
    def unapply(arg: Not): Option[Pattern] = Some(arg._1)
  }


  /**
    * Symbol from the algebra in Matching Logic. Requires a List of [[Pattern]], specified by
    * in the algebra as the number of arguments required to construct the symbol.
    */
  trait Application extends Pattern with LabeledNode[Label] {
    override def apply(_1: Label, args: Seq[Pattern]): Application
  }

  object Application {
    def unapply(arg: Application): Option[(Label, Seq[Pattern])] = Some(arg._1, arg.args)
  }


  /**
    * Matching Logic Implies. Requires two [[Pattern]], represented as _1, and _2.
    */
  trait Implies extends Pattern with Node2 {
    override def apply(_1: Pattern, _2: Pattern): Implies
  }

  object Implies {
    def unapply(arg: Implies): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  /**
    * Matching Logic Existential Quantifier. Requires a [[Variable]] and a [[Pattern]], represented as _1, and _2.
    */
  trait Exists extends Pattern with BinderNode {
    def apply(_1: Variable, _2: Pattern): Exists
  }

  object Exists {
    def unapply(arg: Exists): Option[(Variable, Pattern)] = Some(arg._1, arg._2)
  }


  /**
    * Matching Logic ForAll Quantifier. Requires a [[Variable]] and a [[Pattern]], represented as _1, and _2.
    */
  trait ForAll extends Pattern with BinderNode {
    def apply(_1: Variable, _2: Pattern): ForAll
  }

  object ForAll {
    def unapply(arg: ForAll): Option[(Variable, Pattern)] = Some(arg._1, arg._2)
  }


  /**
    * Matching Logic Next. Requires a [[Pattern]], represented as _1.
    */
  trait Next extends Pattern with Node1 {
    override def apply(_1: Pattern): Next
  }

  object Next {
    def unapply(arg: Next): Option[Pattern] = Some(arg._1)
  }


  /**
    * Matching Logic Rewrite. Requires two [[Pattern]], represented as _1, and _2.
    */
  trait Rewrite extends Pattern with Node2 {
    override def apply(_1: Pattern, _2: Pattern): Rewrite
  }

  object Rewrite {
    def unapply(arg: Rewrite): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  /**
    * Matching Logic Equals. Requires two [[Pattern]], represented as _1, and _2.
    */
  trait Equals extends Pattern with Node2 {
    override def apply(_1: Pattern, _2: Pattern): Equals
  }

  object Equals {
    def unapply(arg: Equals): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }

}

object build {

  import pattern._

  /**
    * The Builders trait has one method for every [[Pattern]], with the same name.
    * Implementations are expected to implement the methods, allowing tools to
    * build patterns in an implementation independent manner.
    */
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

