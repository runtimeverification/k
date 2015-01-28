package org.kframework.tiny

import org.junit.Test
import org.junit.Assert._
import TrueAndFalse._

import org.kframework.kore._
import KORE._

class LogicTest {

  val ab = Equals("a", "b")
  val X = KVariable("X")
  val Y = KVariable("Y")
  val Xa = Equals(X, "a")
  val Xb = Equals(X, "b")
  val Yb = Equals(Y, "b")

  implicit val theory = FreeTheory

  @Test def testAndNormalization {
    assertEquals(And(ab), And(ab))
    assertEquals(And(ab), And(ab, ab))
    assertEquals(And(Set[Predicate](), Map(X -> ("a": K))), And(Xa))
    assertEquals(False, And(Xa, Xb))
  }

  @Test def testAndNotNormalization: Unit = {
    assertEquals(False, theory.normalize(And(ab, Not(ab))))
  }

  @Test def testAndWithTheory {
    implicit val theory = PropositionTheory(ab)
    assertEquals(True, And(Xa, Xb))
  }

  @Test def testPropositionalTheory = {
    assertTrue(PropositionTheory(ab)(ab) == Some(true))
  }
}
