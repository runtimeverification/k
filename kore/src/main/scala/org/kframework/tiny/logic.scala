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
  def estimate(sideConditions: Formula): Int = ???

  /** Solve (up to available data) one of the child formulas */
  def step(sideConditions: Formula): Or = ???
}

object And {
  def apply(formulas: Formula*): And = And(formulas.toSet)
}

case class And(formulas: Set[Formula]) extends Formula {
  /** Estimate the time it takes to solve one variable in one formula */
  def estimate(sideConditions: Formula): Int = ???

  /** Try to solve one variable in one formula */
  def step(sideConditions: Formula): Or = ???
}
