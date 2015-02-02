package org.kframework.tiny

import net.sf.tweety.logics.pl.{syntax => tw}

trait Formula

trait Proposition extends Formula {
  def estimate(sideConditions: Formula): Int
  def step: Or
}

object Or {
  def apply(formulas: Formula*): Or = Or(formulas.toSet)
}

case class Or(formulas: Set[Formula]) extends Formula {
  /** Estimate the time it takes to solve (up to available data) one of the child formulas  */
  def estimate(implicit t: Theory): Int = ???

  /** Solve (up to available data) one of the child formulas */
  def step(implicit t: Theory): Or = ???
}

object And {
  def apply(formulas: Formula*): And = And(formulas.toSet)
}

case class And(formulas: Set[Formula]) extends Formula {
  /** Estimate the time it takes to solve one variable in one formula */
  def estimate(implicit t: Theory): Int = ???

  /** Try to solve one variable in one formula */
  def step(implicit t: Theory): Or = ???
}

case class Binding(a: KVar, b: K) extends Formula
case class Rename(a: KVar, b:KVar) extends Formula