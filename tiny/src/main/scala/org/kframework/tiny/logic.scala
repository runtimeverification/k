package org.kframework.tiny

import org.kframework.attributes.Att
import org.kframework.builtin.Sorts
import org.kframework.kore.Unapply
import org.kframework.tiny.matcher.{MatcherLabel, EqualsMatcher, Matcher}

object Or extends KAssocAppLabel with EmptyAtt {
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new Or(l.toSet, att)

  override def name: String = "OR"

  override def apply(ks: K*): K = super.apply(ks: _*)

  def apply(ks: Set[K], att: Att = Att()): K =
    if (ks.size == 1)
      ks.head
    else
      new Or(ks, att)
}

class Or(val children: Set[K], val att: Att = Att(), normalBy: Option[Theory] = None)
  extends KAssocApp {

  override def isNormalBy(theory: Theory) = children.size == 0 || super.isNormalBy(theory)

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

  override def normalizeInner(implicit theory: Theory): K =
    this.toDNF match {
      case or: Or =>
        val newMe = Or(or.children map {
          _.normalize
        }, att)
        if (EqualsMatcher(newMe, this).normalize == True)
          if (or.children.size == 1)
            or.head
          else
            Or(or.children, att)
        else
          newMe.normalize
      case x => x.normalize
    }

  override def matcher(right: K): Matcher = OrMatcher(this, right)
}

case class OrMatcher(left: Or, right: K) extends Matcher {
  override val klabel: MatcherLabel = OrMatcher

  override def normalizeInner(implicit theory: Theory): K = {
    if (left == Or() && right == Or()) // TODO: understand this
      True
    else
      left map {
        _.matcher(right)
      } normalize
  }
}

object OrMatcher extends MatcherLabel {
  override def apply(k1: K, k2: K, att: Att): KProduct = OrMatcher(k1.asInstanceOf[Or], k2)
}

object And extends KAssocAppLabel with EmptyAtt {
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new And(l.toSet, att)

  override def name: String = "AND"
}

case class And(children: Set[K], att: Att, normalBy: Option[Theory] = None)
  extends KAssocApp {

  override def isNormalBy(theory: Theory) = children.size == 0 || super.isNormalBy(theory)

  /** Estimate the time it takes to solve one variable in one formula */
  def estimate(implicit t: Theory): Int = ???

  /** Try to solve one variable in one formula */
  def step(implicit t: Theory): Or = ???

  // Implementing K
  val klabel = And

  override def normalizeInner(implicit theory: Theory): K = {
    this.toDNF match {
      case and: And =>
        val newMe = and.normalizeChildren
        if (newMe == And() || newMe == Or())
          newMe
        else if (EqualsMatcher(newMe, this).normalize == True)
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

        val newBindings: Map[KVar, K] = normalizedChildren
          .collect { case c: Binding => (c.variable, c.value) }
          .toMap

        import org.kframework.tiny.Substitution._

        val childrenWithSubstitution: Stream[K] = normalizedChildren map {
          _.substitute(newBindings).normalize
        }

        val madeSubstitutions = childrenWithSubstitution.foldLeft(True: K) {
          case (False, _) => False
          case (sum: And, b: Binding) => sum.addBinding(b)
          case (sum: And, c) => And(sum.children + c, sum.att)
        }

        val groundChildren = AsAnd(madeSubstitutions).children filter {
          _.isGround
        }
        val isFalse = (for (c1 <- groundChildren; c2 <- groundChildren) yield (c1, c2))
          .toStream exists { case (c1, c2) => c1 != c2 }

        if (isFalse)
          False
        else
          madeSubstitutions
      }
    }
  }

  lazy val bindings = children collect {
    case b: Binding => b
  }

  lazy val binding: Map[KVar, K] = bindings map {
    case Binding(k, v, _) => (k, v)
  } toMap

  def addBinding(b: Binding)(implicit theory: Theory): K = {
    val newValue = this.binding.get(b.variable).map(existingValue => And(existingValue, b.value).normalize)

    newValue match {
      case None => And(children + b, att)
      case Some(False) => False
      case Some(intersection) => And(
        children map {
          case Binding(v, _, _) if v == b.variable => Binding(b.variable, intersection)
          case x => x
        }, att)
    }
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

  override def normalizeInner(implicit theory: Theory) = a.matcher(b).normalize
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
  extends KProduct with PlainNormalization {
  override def normalizeInner(implicit theory: Theory): K =
    if (!k.isInstanceOf[KVar]) {
      val actualSort: Sort = k.normalize match {
        case s: SortPredicate => Sorts.Bool
        case KApp(l, _, _) => theory.module.sortFor(l)
        case Unapply.KToken(_, sort) => sort
      }
      if (actualSort == klabel.sort ||
        theory.module.subsorts.<(actualSort, klabel.sort))
        TypedKTok(Sorts.Bool, true)
      else
        TypedKTok(Sorts.Bool, false)
    } else {
      super[PlainNormalization].normalizeInner
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