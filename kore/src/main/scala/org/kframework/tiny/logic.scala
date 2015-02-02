package org.kframework.tiny

import net.sf.tweety.logics.pl.{syntax => tw}
import org.kframework.attributes.Att

trait Formula extends K

trait Proposition extends Formula {
  def estimate(sideConditions: Formula): Int
  def step: Or
}

object Or extends KCollectionLabel[Or] {
}

case class Or(children: Set[Formula], att: Att) extends Formula with KCollection {
  /** Estimate the time it takes to solve (up to available data) one of the child formulas  */
  def estimate(implicit t: Theory): Int = ???

  /** Solve (up to available data) one of the child formulas */
  def step(implicit t: Theory): Or = ???

  // Implementing K
  type This = Or
  def label: KCollectionLabel[This] = Or
}

object And extends KCollectionLabel[And] {
}

case class And(chidren: Set[Formula]) extends Formula with KCollection {
  /** Estimate the time it takes to solve one variable in one formula */
  def estimate(implicit t: Theory): Int = ???

  /** Try to solve one variable in one formula */
  def step(implicit t: Theory): Or = ???

  // Implementing K
  type This = And
  def label: KCollectionLabel[This] = And
}

case class Binding(a: K, b: K, att: Att) extends Formula with ProductOfKs {
  override type This = Binding
  override def label = Binding
  override def matcher(right: K): Matcher = ???
}

object Binding extends Label[Binding] {
  override def construct(l: Seq[K], att: Att): Binding = l match {case Seq(a, b) => Binding(a, b, att) }
  val att: Att = Att()
  val name: String = "Binding"
}