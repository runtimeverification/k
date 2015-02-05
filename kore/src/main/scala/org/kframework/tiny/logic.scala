package org.kframework.tiny

import net.sf.tweety.logics.pl.{syntax => tw}
import org.kframework.attributes.Att

object Or extends KAssocAppLabel with EmptyAtt {
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new Or(l.toSet, att)
  override def name: String = "Or"
}

case class Or(children: Set[K], att: Att = Att()) extends KAssocApp {
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
}

object And extends KAssocAppLabel with EmptyAtt {
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new And(l.toSet, att)
  override def name: String = "And"
}

case class And(children: Set[K], att: Att) extends KAssocApp {
  /** Estimate the time it takes to solve one variable in one formula */
  def estimate(implicit t: Theory): Int = ???

  /** Try to solve one variable in one formula */
  def step(implicit t: Theory): Or = ???

  // Implementing K
  val klabel = And

  override def normalize(implicit theory: Theory) = {
    children.map(_.normalize).fold(True) {
      case (sum: And, p: And) =>
        val conflict = (for (
          b1 <- sum.bindings;
          b2 <- p.bindings if b1.variable == b2.variable
        ) yield {
          Equals(b1.value, b2.value).normalize
        }) contains True

        if (conflict)
          False
        else
          And(sum.children | p.children, sum.att)

      case (sum: And, p: Or) =>
        Or((for (m1 <- p.children) yield {
          And(m1, sum).normalize
        }).toSeq: _*)

      case (sum: Or, p: And) => And(p, sum)
      case (sum: Or, p: Or) =>
        Or((for (m1 <- sum.children; m2 <- p.children) yield {
          And(m1, m2)
        }).toSeq: _*)
      case (sum: And, b: Binding) => sum.addBinding(b)
      case (sum: And, p) => And(sum.children + p, sum.att)
      case (sum: Or, p) => And(sum, And(p))
    }
  }

  lazy val bindings = children collect { case b: Binding => b }

  def addBinding(b: Binding)(implicit theory: Theory): K = {
    if (bindings.exists { bb => bb.variable == b.variable && Equals(bb.value, b.value).normalize != True })
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

case class Binding(variable: K, value: K, att: Att) extends KProduct {
  override val klabel = Binding
  override def toString = variable + "->" + value
}

object Binding extends KProduct2Label with EmptyAtt {
  val name: String = "Binding"
}

case class Equals(a: K, b: K, att: Att) extends KProduct {
  override val klabel = Equals
  override def toString = a + "=" + b

  override def normalize(implicit theory: Theory) = a.matcher(b).normalize
}

object Equals extends KProduct2Label with EmptyAtt {
  val name: String = "Equals"
}