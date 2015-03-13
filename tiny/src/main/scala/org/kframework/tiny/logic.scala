package org.kframework.tiny

import org.kframework.attributes.Att
import org.kframework.kore.Unapply
import org.kframework.tiny.matcher.EqualsMatcher

object Or extends KAssocAppLabel with EmptyAtt {
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new Or(l.toSet, att)
  override def name: String = "'_orBool_"
  override def apply(ks: K*): K = super.apply(ks: _*)
  def apply(ks: Set[K], att: Att = Att()): K =
    if (ks.size == 1)
      ks.head
    else
      new Or(ks, att)
}

object OrChildren {
  def unapply(k: K): Option[Set[K]] = k match {
    case or: Or => Some(or.children)
    case k => Some(Set(k))
  }
}

object AndChildren {
  def unapply(k: K): Option[Set[K]] = k match {
    case and: And => Some(and.children)
    case k => Some(Set(k))
  }
}

class Or(val children: Set[K], val att: Att = Att(), normalBy: Option[Theory] = None)
  extends KAssocApp {
  /** Estimate the time it takes to solve (up to available data) one of the child formulas  */
  def estimate(implicit t: Theory): Int = ???

  /** Solve (up to available data) one of the child formulas */
  def step(implicit t: Theory): Or = ???

  // Implementing K
  val klabel: KAssocAppLabel = Or

  override def toString =
    if (children.size == 0)
      "False"
    else if (children.size == 1)
      "||(" + children.head + ")"
    else
      "(" + children.mkString(" || ") + ")"

  override def normalizeInner(implicit theory: Theory): K = this.toDNF.eliminateGroundBooleans match {
    case or: Or =>
      val newMe = Or(or.children map { _.normalize }, att)
      if (EqualsMatcher(newMe, this).normalize == True)
        if (or.children.size == 1)
          or.head
        else
          Or(or.children, att)
      else
        newMe.normalize
    case x => x.normalize
  }
}

object And extends KAssocAppLabel with EmptyAtt {
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new And(l.toSet, att)
  override def name: String = "'_andBool_"
}

case class And(children: Set[K], att: Att, normalBy: Option[Theory] = None)
  extends KAssocApp {

  /** Estimate the time it takes to solve one variable in one formula */
  def estimate(implicit t: Theory): Int = ???

  /** Try to solve one variable in one formula */
  def step(implicit t: Theory): Or = ???

  // Implementing K
  val klabel = And

  override def normalizeInner(implicit theory: Theory): K = {
    val dnf = this.toDNF.eliminateGroundBooleans
    dnf match {
      case and: And =>
        val newMe = and.normalizeChildren
        if (EqualsMatcher(newMe, this).normalize == True)
          if (and.children.size == 1)
            and.head
          else
            And(and.children, att, Some(theory))
        else
          newMe.normalize
      case x => x.normalize
    }
  }

  def normalizeChildren(implicit theory: Theory): K = {
    if (children.toStream.exists(_.isFalse))
      False
    else {
      // working with streams to stop at first conflict
      val normalizedChildren: Stream[K] = children.toStream map {
        _.normalize
      }

      if (normalizedChildren.contains(False))
        False
      else {
        // this could be optimized to only consider new children but it somehow doesn't work
        // will look into it another time. We could use newChildren to find bindings instead
        // of normalizedChildren.
        //    val newChildren = normalizedChildren -- children

        val newBindings: Map[KVar, K] = normalizedChildren collect {
          case c: Binding => (c.variable, c.value)
        } toMap

        import org.kframework.tiny.Substitution._

        val childrenWithSubstitution: Stream[K] = normalizedChildren map {
          c =>
            c.substitute(newBindings).normalize
        }

        childrenWithSubstitution.foldLeft(True: K) {
          case (False, _) => False
          case (sum: And, b: Binding) => sum.addBinding(b)
          case (sum: And, c) => And(sum.children + c, sum.att)
        }
      }
    }
  }

  def eliminateGroundBooleans: K = if (children.contains(False)) False else this

  //    children.foldLeft(True: K) {
  //    case (_, False) => False
  //    //    case (sum, TypedKTok(Sorts.Bool, false, _)) => False
  //    case (False, _) => False
  //    case (sum, True) => sum
  //    //    case (sum, TypedKTok(Sorts.Bool, true, _)) => sum
  //    case (sum, Or(True, _, _)) => sum
  //    case (sum: And, p) => And(sum.children + p, sum.att)
  //  }


  def addBinding(b: Binding)(implicit theory: Theory): K = {
    if (this.bindings.exists {
      bb => bb.variable == b.variable && Equals(bb.value, b.value).normalize != True
    })
      False
    else
      And(children + b, att)
  }

  override def toString =
    if (children.size == 0)
      "True"
    else if (children.size == 1)
      "&&(" + children.head + ")"
    else
      "(" + children.mkString(" && ") + ")"
}

case class Binding(variable: KVar, value: K, att: Att) extends KProduct with PlainNormalization {

  assert(variable != value)

  override val klabel = Binding
  override def toString = variable + "->" + value
}

object Binding extends KProduct2Label with EmptyAtt {
  val name: String = "Binding"
  override def apply(k1: K, k2: K, att: Att): KProduct = Binding(k1.asInstanceOf[KVar], k2, att)
}

case class Equals(a: K, b: K, att: Att) extends KProduct {
  override val klabel = Equals
  override def toString = a + "=" + b

  override def normalizeInner(implicit theory: Theory) = EqualsMatcher(a, b)
}

object Equals extends KProduct2Label with EmptyAtt {
  val name: String = "Equals"
}

case class Not(k: K, att: Att = Att()) extends KProduct {
  override val klabel = Not
  override def toString = "!" + k

  override def normalizeInner(implicit theory: Theory) = k.normalize match {
    case True => False
    case False => True
    case x => Not(x, att)
  }
}

object Not extends KProduct1Label with EmptyAtt {
  val name: String = "!"
}

case class SortPredicate(klabel: SortPredicateLabel, k: K, att: Att = Att())
  extends KProduct {
  override protected[this] def normalizeInner(implicit theory: Theory): K =
    if (!k.isInstanceOf[KVar]) {
      val actualSort = k match {
        case KApp(l, _, _) => theory.asInstanceOf[TheoryWithUpDown].module.sortFor(l)
        case Unapply.KToken(s, _) => s
      }
      if (actualSort == klabel.sort ||
        theory.asInstanceOf[TheoryWithUpDown].module.subsorts.<(actualSort, klabel.sort))
        True
      else
        False
    } else {
      this
    }
}

object SortPredicate {
  def apply(s: Sort, k: K) = SortPredicateLabel(s)(k)
}

case class SortPredicateLabel(sort: Sort) extends KRegularAppLabel {
  assert(sort != null)
  override def att: Att = Att()
  override def name: String = "is" + sort.name
  override def construct(l: Iterable[K], att: Att): KApp = l match {
    case Seq(k) => SortPredicate(this, k, att)
  }
}