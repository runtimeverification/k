package org.kframework.tiny

import org.kframework.attributes.Att
import org.kframework.kore.{Unapply, Unparse}
import org.kframework.tiny.matcher.EqualsMatcher

trait Logic extends K {
  def toDNF: Logic
  def eliminateGroundBooleans: Logic
}

object Or extends KAssocAppLabel with EmptyAtt {
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new Or(l.toSet, att)
  override def name: String = "'_orBool_"
  override def apply(ks: K*): Or = super.apply(ks: _*).asInstanceOf[Or]
}

trait NormalizationCache {
  self: K =>

  val normalBy: Option[Theory]
  def normalizeInner(implicit theory: Theory) = normalBy match {
    case Some(`normalBy`) => this
    case _ =>
      if (this == True || this == False)
        this
      else
        actualNormalize
  }
  def actualNormalize(implicit theory: Theory): K
}

case class Or(children: Set[K], att: Att = Att(), normalBy: Option[Theory] = None)
  extends KAssocApp with Logic with NormalizationCache {
  /** Estimate the time it takes to solve (up to available data) one of the child formulas  */
  def estimate(implicit t: Theory): Int = ???

  /** Solve (up to available data) one of the child formulas */
  def step(implicit t: Theory): Or = ???

  // Implementing K
  val klabel: KAssocAppLabel = Or

  override def toString =
    if (children.size == 0)
      "False"
    else
      "(" + children.mkString(" || ") + ")"

  override def normalizeInner(implicit theory: Theory) = super[NormalizationCache].normalizeInner

  def toDNF: Logic = toDNF(False, children.toSeq).eliminateGroundBooleans

  private def toDNF(start: Logic, children: Seq[K]): Logic = children.foldLeft(start: Logic) {
    case (sum: Or, p: Or) => toDNF(sum, p.children.toSeq)
    case (sum: Or, p: And) => p.toDNF match {
      case or: Or => Or(sum.children ++ or.children)
      case p: And => Or(sum.children + p)
    }
    case (sum: Or, p) => new Or(sum.children + And(p))
  }

  def eliminateGroundBooleans: Logic = children.foldLeft(False: Logic) {
    case (_, True) => Or(True)
//    case (sum, TypedKTok(Sorts.Bool, true, _)) => Or(True)
    case (True, _) => Or(True)
    case (sum: Or, False) => sum
//    case (sum, TypedKTok(Sorts.Bool, false, _)) => sum
    case (sum: Or, p) => Or(sum.children + p)
  }

  override def actualNormalize(implicit theory: Theory): K = toDNF.eliminateGroundBooleans match {
    case or: Or =>
      val newMe = Or(or.children map { _.normalize }, att)
      if (EqualsMatcher(newMe, this).normalize == True)
        Or(or.children, att, Some(theory))
      else
        newMe.normalize
    case x => x.normalize
  }
}

object And extends KAssocAppLabel with EmptyAtt {
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new And(l.toSet, att)
  override def name: String = "'_andBool_"
  override def apply(ks: K*): And = super.apply(ks: _*).asInstanceOf[And]
}

case class And(children: Set[K], att: Att, normalBy: Option[Theory] = None)
  extends KAssocApp with Logic with NormalizationCache {

  /** Estimate the time it takes to solve one variable in one formula */
  def estimate(implicit t: Theory): Int = ???

  /** Try to solve one variable in one formula */
  def step(implicit t: Theory): Or = ???

  // Implementing K
  val klabel = And

  override def normalizeInner(implicit theory: Theory) = super[NormalizationCache].normalizeInner

  def actualNormalize(implicit theory: Theory): K = {
    val dnf = toDNF.eliminateGroundBooleans
    dnf match {
      case and: And =>
        val newMe = and.normalizeChildren
        if (EqualsMatcher(newMe, this).normalize == True)
          And(and.children, att, Some(theory))
        else
          newMe.normalize
      case x => x.normalize
    }
  }

  def normalizeChildren(implicit theory: Theory): Logic = {
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

        childrenWithSubstitution.foldLeft(True: Logic) {
          case (False, _) => False
          case (sum: And, b: Binding) => sum.addBinding(b)
          case (sum: And, c) => And(sum.children + c, sum.att)
        }
      }
    }
  }

  def toDNF: Logic = {
    val res = toDNF(True, children.toSeq)

    res match {
      case and: And => assert(!and.children.exists(c => c.isInstanceOf[And] || (c.isInstanceOf[Or] && c != False)),
        Unparse(and))
      case _ =>
    }

    res
  }

  def toDNF(start: Logic, c: Seq[K]): Logic =
    c.foldLeft(start) {
      case (sum: And, or: Or) =>
        Or((for (m1 <- or.children) yield {
          And(m1, sum).toDNF
        }).toSeq: _*).toDNF
      case (sum: And, p: And) => toDNF(sum, p.children.toSeq)
      case (sum: And, p) => new And(sum.children + p, sum.att)

      case (sum: Or, p: And) => toDNF(p, Seq(sum))
      case (sum: Or, p: Or) =>
        Or((for (m1 <- sum.children;
                 m2 <- p.children) yield {
          And(m1, m2).toDNF
        }).toSeq: _*).toDNF
      case (sum: Or, p) => toDNF(And(p), Seq(sum))
    }


  override def eliminateGroundBooleans: Logic = children.foldLeft(True: Logic) {
    case (_, False) => False
//    case (sum, TypedKTok(Sorts.Bool, false, _)) => False
    case (False, _) => False
    case (sum, True) => sum
//    case (sum, TypedKTok(Sorts.Bool, true, _)) => sum
    case (sum, Or(True, _, _)) => sum
    case (sum: And, p) => And(sum.children + p, sum.att)
  }


  lazy val bindings = children collect {
    case b: Binding => b
  }

  lazy val binding: Map[KVar, K] = bindings map {
    case Binding(k, v, _) => (k, v)
  } toMap

  lazy val isPureSubsitution: Boolean = binding.size == children.size

  def addBinding(b: Binding)(implicit theory: Theory): Logic = {
    if (bindings.exists {
      bb => bb.variable == b.variable && Equals(bb.value, b.value).normalize != True
    })
      False
    else
      And(children + b, att)
  }

  override def toString =
    if (children.size == 0)
      "True"
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