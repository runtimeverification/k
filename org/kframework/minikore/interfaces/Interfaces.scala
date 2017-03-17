package org.kframework.minikore.interfaces

/**
  * Provides a collection of [[tree.AST]] types, allowing for viewing [[pattern.Pattern]]s as ASTs.
  *
  * Sample Usage -
  * {{{def printVariableNames(pattern: Pattern): Unit = p match {
  *     case BinderNode(Variable(str: Name, Sort(sortName)), p: Pattern) => {
  *       println(Name +"@" + sortName)
  *       printVariableName(p)
  *     }
  *     case Node(args: Seq[Pattern]) => args.map(printVariableNames)
  *     case Variable(str: Name, Sort(sortName)) => println(str + "@" sortName)
  *   }
  * }}}
  *
  *
  */
object tree {

  import pattern._

  /**
    * Base type of the Tree interface. [[pattern.Pattern]] extends AST.
    * Represents a Pattern in Matching Logic.
    */
  trait AST


  /**
    * Specifies Node behavior of [[pattern.Pattern]].
    *
    * Allows matching a Pattern against as a Node,
    * and building a Pattern from a list of Patterns.
    */
  trait Node extends AST with Product {
    def args: Seq[Pattern]

    /* Allows building Nodes using a list of Patterns */
    def build(children: Seq[Pattern]): Pattern
  }

  object Node {
    def unapply(arg: Node): Option[Seq[Pattern]] = Some(arg.args)
  }


  /**
    * Specifies Leaf Behavior of Patterns.
    *
    * @tparam C The Contents of the Leaf.
    */
  trait Leaf[C] extends AST with Product {
    def contents: C

    /* Allows building a leaf using its contents */
    def build(contents: C): Pattern
  }

  object Leaf {
    def unapply[C](arg: Leaf[C]): Option[C] = Some(arg.contents)
  }


  /**
    * A Leaf with Product2[CC1, CC2] as its contents. [[pattern.DomainValue]], [[pattern.Variable]] extend this trait.
    *
    * [[Leaf2]] extends [[Leaf]], with Product[CC1, CC2] as its type parameter.
    * This allows for creating a Leaf[Product[CC1, CC2]], directly using the build method, of
    * type (CC1, CC2) => Pattern.
    *
    * @tparam CC1 Type of First Field.
    * @tparam CC2 Type of Second Field.
    */
  sealed trait Leaf2[CC1, CC2] extends Leaf[Product2[CC1, CC2]] with Product2[CC1, CC2] {
    override def contents: Product2[CC1, CC2] = (_1, _2)

    def build(_1: CC1, _2: CC2): Pattern

    override def build(contents: Product2[CC1, CC2]): Pattern = build(contents._1, contents._2)
  }

  object Leaf2 {
    def unapply[CC1, CC2](arg: Leaf2[CC1, CC2]): Option[(CC1, CC2)] = Some(arg._1, arg._2)
  }


  /**
    * Node with extra member label, respresenting a node's Label. [[pattern.Application]] that extends this trait.
    *
    * @tparam L Type of Label.
    */
  sealed trait LabeledNode[L] extends Node with Product1[L] {
    def build(_1: L, args: Seq[Pattern]): Pattern

    override def build(children: Seq[Pattern]): Pattern = build(_1, children)
  }

  object LabeledNode {
    def unapply[L](arg: LabeledNode[L]): Option[(L, Seq[Pattern])] = Some(arg._1, arg.args)
  }


  /**
    * A Node with empty list of Patterns as its args list. [[pattern.Top]], [[pattern.Bottom]] extend this trait.
    */
  sealed trait Node0 extends Node {
    override def args = Seq.empty[Pattern]

    def build(): Pattern

    override def build(children: Seq[Pattern]): Pattern = {
      assert(children.isEmpty)
      build()
    }
  }

  object Node0 {
    def unapply(arg: Node0): Boolean = true
  }


  /**
    * A Node with a single pattern in its args list. Extended by [[pattern.Next]], [[pattern.Not]].
    */
  sealed trait Node1 extends Node with Product1[Pattern] {
    override def args = Seq(_1)

    def build(_1: Pattern): Pattern

    override def build(children: Seq[Pattern]): Pattern = {
      assert(children.size == 1)
      build(children.head)
    }
  }

  object Node1 {
    def unapply(arg: Node1): Option[Pattern] = Some(arg._1)
  }


  /**
    * A Node with two Patterns in its args list. Extended by [[pattern.Or]], [[pattern.And]], [[pattern.Implies]], [[pattern.Equals]], [[pattern.Rewrite]].
    */
  sealed trait Node2 extends Node with Product2[Pattern, Pattern] {
    def build(_1: Pattern, _2: Pattern): Pattern

    override def args = Seq(_1, _2)

    override def build(children: Seq[Pattern]): Pattern = {
      assert(children.size == 2)
      build(children.head, children(1))
    }
  }

  object Node2 {
    def unapply(arg: Node2): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  /**
    * Extends [[Node2]], and only allows [[pattern.Variable]] as the first element, and [[pattern.Pattern]] in its args list. Extended by [[pattern.Exists]], [[pattern.ForAll]].
    *
    * TODO: An extension of Binder Node may be provided in the future, to allow user defined symbols to have binder-like behavior.
    *       These symbols may allow multiple arguments, with the variable bound in some, but not all of them.
    */
  sealed trait BinderNode extends Node2 {
    def build(_1: Variable, _2: Pattern): Pattern

    override val _1: Variable

    override def build(_1: Pattern, _2: Pattern): Pattern = build(_1.asInstanceOf[Variable], _2)

    override def build(children: Seq[Pattern]): Pattern = {
      assert(children.size == 2)
      build(children.head.asInstanceOf[Variable], children(1))
    }
  }

  object BinderNode {
    def unapply(arg: BinderNode): Option[(Variable, Pattern)] = Some(arg._1, arg._2)
  }

}

/**
  * Provides all Pattern types, and destructors for matching on [[pattern.Pattern]]s.
  *
  * Sample Usage -
  * {{{
  *   def filterAndConstructs(patterns: Seq[Pattern]): Seq[Pattern] = patterns collect {
  *     case a@And(x: Pattern, y: Pattern) => a
  *   }
  * }}}
  *
  */
object pattern {

  import tree._

  /* ML Pattern Type */
  trait Pattern extends AST


  /**
    * Matching Logic Variable.
    *
    * Provides (Implementations for members)
    *    - contents of type Product2[Name, Sort].
    *
    * Requires (Implementation for members)
    *    - _1 of type [[Name]].
    *    - _2 of type [[Sort]].
    *    - build method taking arguments ([[Name]], [[Sort]]) and returning [[Variable]].
    */
  trait Variable extends Pattern with Leaf2[Name, Sort] {
    def build(_1: Name, _2: Sort): Variable
  }

  object Variable {
    def unapply(arg: Variable): Option[(Name, Sort)] = Some(arg._1, arg._2)
  }

  trait Symbol {
    def str: String
  }

  object Symbol {
    def unapply(s: Symbol) = Some(s.str)
  }

  case class Sort(str: String)

  type Value = String

  type Name = String


  /**
    * Matching Logic DomainValue.
    *
    * Provides (Implementations for members)
    *    - contents of type Product2[Symbol, Value].
    *
    * Requires (Implementation for members)
    *    - _1 of type [[Symbol]].
    *    - _2 of type [[Value]].
    *    - build method taking arguments ([[Symbol]], [[Value]]) and returning [[DomainValue]].
    */
  trait DomainValue extends Pattern with Leaf2[Symbol, Value] {
    def build(_1: Symbol, _2: Value): DomainValue
  }

  object DomainValue {
    def unapply(arg: DomainValue): Option[(Symbol, Value)] = Some(arg._1, arg._2)
  }


  /**
    * Matching Logic Top.
    *
    * Provides (Implementation for members)
    *    - args, an empty list.
    *
    * Requires (Implementation for members)
    *    - build method taking arguments () and returning [[Top]].
    */
  trait Top extends Pattern with Node0 {
    override def build(): Top
  }

  object Top {
    def unapply(arg: Top): Boolean = true
  }


  /**
    * Matching Logic Bottom.
    *
    * Provides (Implementation for members)
    *    - args, an empty list.
    *
    * Requires (Implementation for members)
    *    - build method taking arguments () and returning [[Bottom]].
    */
  trait Bottom extends Pattern with Node0 {
    override def build(): Bottom
  }

  object Bottom {
    def unapply(arg: Bottom): Boolean = true
  }


  /**
    * Matching Logic And.
    *
    * Provides (Implementation for members)
    *    - args, a list containing two [[Pattern]]s.
    *
    * Requires (Implementation for members)
    *    - _1 of type [[Pattern]].
    *    - _2 of type [[Pattern]].
    *    - build method taking arguments ([[Pattern]], [[Pattern]]) and returning [[And]].
    */
  trait And extends Pattern with Node2

  object And {
    def unapply(arg: And): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  /**
    * Matching Logic Or.
    *
    * Provides (Implementation for members)
    *    - args, a list containing two [[Pattern]]s.
    *
    * Requires (Implementation for members)
    *    - _1 of type [[Pattern]].
    *    - _2 of type [[Pattern]].
    *    - build method taking arguments ([[Pattern]], [[Pattern]]) and returning [[Or]].
    */
  trait Or extends Pattern with Node2

  object Or {
    def unapply(arg: Or): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  /**
    * Matching Logic Not.
    *
    * Provides (Implementation for members)
    *    - args, a list containing one [[Pattern]].
    *
    * Requires (Implementation for members)
    *    - _1 of type [[Pattern]].
    *    - build method taking argument ([[Pattern]]) and returning [[Not]].
    */
  trait Not extends Pattern with Node1

  object Not {
    def unapply(arg: Not): Option[Pattern] = Some(arg._1)
  }


  /**
    * Matching Logic Symbol Application.
    *
    * Requires (Implementation for members)
    *    - _1 of type [[Symbol]], representing symbol from Matching Logic Algebra.
    *    - args of type Seq[Pattern].
    *    - build method taking arguments ([[Symbol]], Seq[Pattern]) and returning [[Application]].
    */
  trait Application extends Pattern with LabeledNode[Symbol]

  object Application {
    def unapply(arg: Application): Option[(Symbol, Seq[Pattern])] = Some(arg._1, arg.args)
  }


  /**
    * Matching Logic Implies.
    *
    * Provides (Implementation for members)
    *    - args, a list containing two [[Pattern]]s.
    *
    * Requires (Implementation for members)
    *    - _1 of type [[Pattern]].
    *    - _2 of type [[Pattern]].
    *    - build method taking arguments ([[Pattern]], [[Pattern]]) and returning [[Implies]].
    */
  trait Implies extends Pattern with Node2

  object Implies {
    def unapply(arg: Implies): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  /**
    * Matching Logic Existential Quantifier.
    *
    * Provides (Implementation for members)
    *    - args, a list containing a [[Variable]] and a [[Pattern]].
    *
    * Requires (Implementation for members)
    *    - _1 of type [[Variable]].
    *    - _2 of type [[Pattern]].
    *    - build method taking arguments ([[Variable]], [[Pattern]]) and returning [[Exists]].
    */
  trait Exists extends Pattern with BinderNode

  object Exists {
    def unapply(arg: Exists): Option[(Variable, Pattern)] = Some(arg._1, arg._2)
  }


  /**
    * Matching Logic ForAll Quantifier.
    *
    * Provides (Implementation for members)
    *    - args, a list containing a [[Variable]] and a [[Pattern]].
    *
    * Requires (Implementation for members)
    *    - _1 of type [[Variable]].
    *    - _2 of type [[Pattern]].
    *    - build method taking arguments ([[Variable]], [[Pattern]]) and returning [[ForAll]].
    */
  trait ForAll extends Pattern with BinderNode

  object ForAll {
    def unapply(arg: ForAll): Option[(Variable, Pattern)] = Some(arg._1, arg._2)
  }


  /**
    * Matching Logic Next.
    *
    * Provides (Implementation for members)
    *    - args, a list containing one [[Pattern]].
    *
    * Requires (Implementation for members)
    *    - _1 of type [[Pattern]].
    *    - build method taking argument ([[Pattern]]) and returning [[Next]].
    */
  trait Next extends Pattern with Node1

  object Next {
    def unapply(arg: Next): Option[Pattern] = Some(arg._1)
  }


  /**
    * Matching Logic Rewrite.
    *
    * Provides (Implementation for members)
    *    - args, a list containing two [[Pattern]]s.
    *
    * Requires (Implementation for members)
    *    - _1 of type [[Pattern]].
    *    - _2 of type [[Pattern]].
    *    - build method taking arguments ([[Pattern]], [[Pattern]]) and returning [[Rewrite]].
    */
  trait Rewrite extends Pattern with Node2

  object Rewrite {
    def unapply(arg: Rewrite): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }


  /**
    * Matching Logic Equals.
    *
    * Provides (Implementation for members)
    *   - args, a list containing two [[Pattern]]s.
    *
    * Requires (Implementation for members)
    *   - _1 of type [[Pattern]].
    *   - _2 of type [[Pattern]].
    *   - build method taking arguments ([[Pattern]], [[Pattern]]) and returning [[Equals]].
    */
  trait Equals extends Pattern with Node2

  object Equals {
    def unapply(arg: Equals): Option[(Pattern, Pattern)] = Some(arg._1, arg._2)
  }

}

/**
  * Provides a Builder type that allows building Pattern types in [[pattern]].
  *
  * Sample Usage -
  *
  * Given a concrete implementation of [[build.Builders]], one can create new patters -
  * {{{
  *   /* Given Concrete Implementation */
  *   val builder: Builders = ConcreteBuilders
  *   /* A Pattern Or(X:Int, Y:Int) can be constructed in the following way */
  *   val or: Or = builder.Or(builder.Variable("X", Sort("Int")), builder."Y", Sort("Int"))
  * }}}
  *
  */
object build {

  import pattern._

  /**
    * The Builders trait has one method for every [[pattern.Pattern]], with the same name.
    * Implementations are expected to implement the methods, allowing tools to
    * build patterns in an implementation independent manner.
    */
  trait Builders {

    def Symbol(str: String): Symbol

    def Variable(_1: Name, _2: Sort): Variable

    def DomainValue(_1: Symbol, _2: Value): DomainValue

    def Top(): Top

    def Bottom(): Bottom

    def Not(_1: Pattern): Pattern

    def Next(_1: Pattern): Pattern

    def And(_1: Pattern, _2: Pattern): Pattern

    def Or(_1: Pattern, _2: Pattern): Pattern

    def Implies(_1: Pattern, _2: Pattern): Pattern

    def Equals(_1: Pattern, _2: Pattern): Pattern

    def Exists(_1: Variable, _2: Pattern): Pattern

    def ForAll(_1: Variable, _2: Pattern): Pattern

    def Rewrite(_1: Pattern, _2: Pattern): Pattern

    def Application(_1: Symbol, args: Seq[Pattern]): Pattern
  }

}

