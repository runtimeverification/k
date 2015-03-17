package org.kframework.tiny

import org.junit.Test

class LogicTest extends AbstractTest {

  import cons._

  @Test def nestingOfAndOr {
    implicit val theory = FreeTheory
    assertEquals(Or(And(X)), And(Or(And(Or(And(X))))).normalize)
    assertEquals(Or(And(Binding(X, 'foo()))), And(Or(And(Or(Binding(X, 'foo()))))).normalize)
  }

  @Test def notProperty {
    implicit val theory = FreeTheory
    assertEquals(True, Not(False).normalize)
    assertEquals(False, Not(True).normalize)
    assertEquals(Not('foo(X)), Not('foo(X)).normalize)
    assertEquals(Not('foo()), Not('foo()).normalize)
  }
}
