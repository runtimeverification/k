package org.kframework.tiny

import org.kframework.attributes.Att
import org.kframework.kore.Unparse

trait Logic extends K {
  def toDNF: Logic
  def eliminateGroundBooleans: Logic
}

object Or extends KAssocAppLabel with EmptyAtt {
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new Or(l.toSet, att)
  override def name: String = "Or"
  override def apply(ks: K*): Or = super.apply(ks: _*).asInstanceOf[Or]
}

trait NormalizationCache {
  self: K =>

  val normalBy: Option[Theory]
  def normalize(implicit theory: Theory) = normalBy match {
    case Some(`normalBy`) => this
    case _ =>
      if (this == True || this == False)
        this
      else
        actualNormalize
  }
  def actualNormalize(implicit theory: Theory): K
}

case class Or(children: Set[K], att: Att = Att(), normalBy: Option[Theory] = None) extends KAssocApp with Logic with
NormalizationCache {
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

  override def normalize(implicit theory: Theory) = super[NormalizationCache].normalize

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
    case (True, _) => Or(True)
    case (sum: Or, False) => sum
    case (sum: Or, p) => Or(sum.children + p)
  }

  override def actualNormalize(implicit theory: Theory): K = toDNF.eliminateGroundBooleans match {
    case or: Or =>
      val newMe = Or(or.children map { _.normalize }, att)
      if (theory.equals(newMe, this) == True)
        Or(or.children, att, Some(theory))
      else
        newMe.normalize
    case x => x.normalize
  }
}

object And extends KAssocAppLabel with EmptyAtt {
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new And(l.toSet, att)
  override def name: String = "And"
  override def apply(ks: K*): And = super.apply(ks: _*).asInstanceOf[And]
}

case class And(children: Set[K], att: Att, normalBy: Option[Theory] = None) extends KAssocApp with Logic with
NormalizationCache {

  /** Estimate the time it takes to solve one variable in one formula */
  def estimate(implicit t: Theory): Int = ???

  /** Try to solve one variable in one formula */
  def step(implicit t: Theory): Or = ???

  // Implementing K
  val klabel = And

  override def normalize(implicit theory: Theory) = super[NormalizationCache].normalize

  def actualNormalize(implicit theory: Theory): K = {
    val dnf = toDNF.eliminateGroundBooleans
    dnf match {
      case and: And =>
        val newMe = and.normalizeChildren
        if (theory.equals(newMe, this) == True)
          And(and.children, att, Some(theory))
        else
          newMe.normalize
      case x => x.normalize
    }
  }

  def normalizeChildren(implicit theory: Theory): Logic = {
    // working with streams to stop at first conflict
    val normalizedChildren = children map {
      _.normalize
    }

    val newChildren = normalizedChildren -- children

    val newBindings = newChildren collect {
      case c: Binding => (c.variable, c.value)
    } toMap

    import org.kframework.tiny.Substitution._

    val childrenWithSubstitution = normalizedChildren map {
      c =>
        c.substitute(newBindings)
    }

    childrenWithSubstitution.foldLeft(True: Logic) {
      case (False, _) => False
      case (sum: And, b: Binding) => sum.addBinding(b)
      case (sum: And, c) => And(sum.children + c, sum.att)
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
    case (False, _) => False
    case (sum, True) => sum
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

case class Binding(variable: KVar, value: K, att: Att) extends KProduct {
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

  override def normalize(implicit theory: Theory) = a.matcher(b).normalize
}

object Equals extends KProduct2Label with EmptyAtt {
  val name: String = "Equals"
}