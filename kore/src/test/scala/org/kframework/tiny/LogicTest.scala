package org.kframework.tiny

import net.sf.tweety.logics.pl.{syntax => tw}
import org.junit.Test

class LogicTest extends AbstractTest {
  @Test def nestingOfAndOr {
    implicit val theory = FreeTheory
    assertEquals(And(X), And(Or(And(Or(And(X))))).normalize)
    assertEquals(And(Binding(X, X)), And(Or(And(Or(Binding(X, X))))).normalize)
  }
}
