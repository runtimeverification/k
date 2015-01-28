package org.kframework.tiny.foo

import net.sf.tweety.logics.pl.sat.Sat4jSolver
import net.sf.tweety.logics.pl.syntax._
import org.junit.Test


/**
 * Created by cos on 1/28/15.
 */
class TweetyTest {

  val solver = new Sat4jSolver()

  def and(a: PropositionalFormula, b: PropositionalFormula) = new Conjunction(a, b)

  def or(a: PropositionalFormula, b: PropositionalFormula) = new Disjunction(a, b)

  def not(a: PropositionalFormula) = new Negation(a)


  @Test def simple {
    val a = new Proposition("a")
    val b = new Proposition("b")
    val T = new Tautology

    println(solver.isConsistent(and(a, not(a)): PropositionalFormula))
  }

  @Test def simple1 {
    val a = new Proposition("a")
    val b = new Proposition("b")
    val T = new Tautology

    println(solver.isConsistent(and(a, not(a)): PropositionalFormula))
  }
}
