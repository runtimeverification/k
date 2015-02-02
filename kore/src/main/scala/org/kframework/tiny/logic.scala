package org.kframework.tiny

import net.sf.tweety.logics.pl.{syntax => tw}
import org.kframework.attributes.Att

object Or extends KAssocAppLabel with EmptyAtt {
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new Or(l.toSet, att)
  override def name: String = "Or"
}

case class Or(children: Set[K], att: Att) extends KAssocApp {
  /** Estimate the time it takes to solve (up to available data) one of the child formulas  */
  def estimate(implicit t: Theory): Int = ???

  /** Solve (up to available data) one of the child formulas */
  def step(implicit t: Theory): Or = ???

  // Implementing K
  def klabel: KAssocAppLabel = Or
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
  def klabel = And
}

case class Binding(a: K, b: K, att: Att) extends KProduct {
  override def klabel = Binding
  override def matcher(right: K): Matcher = ???
}

object Binding extends Label {
  override def construct(l: Iterable[K], att: Att): Binding = l match {case Seq(a, b) => Binding(a, b, att) }
  val att: Att = Att()
  val name: String = "Binding"
}