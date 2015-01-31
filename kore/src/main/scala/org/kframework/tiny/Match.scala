package org.kframework.tiny

trait Match extends Formula {
  /** Estimate the time it takes to solve one variable */
  def estimate(sideConditions: Formula): Int = ???
  /** Solve one variable */
  def step(sideConditions: Formula): Or = ???
}
