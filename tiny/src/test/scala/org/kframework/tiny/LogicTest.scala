package org.kframework.tiny

import org.junit.Test

class LogicTest extends AbstractTest {
  @Test def nestingOfAndOr {
    implicit val theory = FreeTheory
    assertEquals(Or(And(X)), And(Or(And(Or(And(X))))).normalize)
    assertEquals(Or(And(Binding(X, X))), And(Or(And(Or(Binding(X, X))))).normalize)
  }
}
