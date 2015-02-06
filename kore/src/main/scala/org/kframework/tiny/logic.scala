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

  override def normalize(implicit theory: Theory) =
    children.map(_.normalize).foldLeft(False: K) {
      case (sum: Or, True) =>
        Or(True)
      case (sum: Or, False) =>
        sum
      case (True, p) =>
        Or(True)
      case (sum: Or, p: Or) =>
        new Or(sum.children | p.children)
      case (sum: Or, p: And) =>
        new Or(sum.children + p)
      case (sum: Or, p) =>
        new Or(sum.children + And(p).asInstanceOf[And])
    }
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
      case (sum: And, False) => False
      case (sum: And, True) => sum
      case (True, or: Or) => or
      case (False, or: Or) => False
      case (sum: And, p: And) =>
        // working with streams to stop at first conflict
        val conflict: Stream[Boolean] = for (
          b1 <- sum.bindings.toStream;
          b2 <- p.bindings.toStream if b1.variable == b2.variable;
          r = true if Equals(b1.value, b2.value).normalize == True
        ) yield {r }

        if (!conflict.isEmpty)
          False
        else
          new And(sum.children | p.children, sum.att)

      case (sum: And, or: Or) =>
        Or((for (m1 <- or.children) yield {
          And(m1, sum).normalize
        }).toSeq: _*)

      case (sum: Or, p: And) => And(p, sum).normalize
      case (sum: Or, p: Or) =>
        Or((for (m1 <- sum.children; m2 <- p.children) yield {
          And(m1, m2).normalize
        }).toSeq: _*).normalize
      case (sum: And, b: Binding) => sum.addBinding(b)
      case (sum: And, p) => new And(sum.children + p, sum.att)
      case (sum: Or, p) => And(p, sum).normalize
    }
  }

  lazy val bindings = children collect {
    case b: Binding => b
  }

  def addBinding(b: Binding)(implicit theory: Theory): K = {
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