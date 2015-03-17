package org.kframework.tinytest

import org.junit.Test
import org.kframework.builtin.Sorts
import org.kframework.tiny.AbstractTest
import org.kframework.tiny.builtin.KMapAppLabel

class ADTTest extends AbstractTest {

  import cons._
  import org.kframework.builtin.Labels
  import org.kframework.tiny._

  val labels = new Labels(cons)

  val seqX2 = X ~> 2
  val rew = (1: K) ==> 2


  @Test def equalities {
    assertEquals(2: K, 2: K)
    assertEquals(X, KVariable("X"))
    assertEquals(seqX2, X ~> 2)
    assertNotEquals(seqX2, X ~> X ~> 2)
    assertEquals(KSequence(X, X, 2), KSequence(X, KSequence(X, 2)))
    assertEquals(KSequence(X, X, 2), KSequence(KSequence(X, X), 2))
    assertEquals('foo(), KLabel("foo")())
    assertNotEquals('foo(), KLabel("bar")())
    assertNotEquals('foo(), KLabel("foo")(X))

    val divide = NativeBinaryOpLabel("/", Att(), (x: Int, y: Int) => x / y, Sorts.Int)

    assertEquals(5: K, divide(10, 2).normalize)
    assertEquals(KSequence(5: K), KSequence(divide(10, 2)).normalize)
    assertEquals('foo(KSequence(5: K)), 'foo(KSequence(divide(10, 2))).normalize)
    assertEquals(And('foo(KSequence(5: K))), And('foo(divide(10, 2))).normalize)
    assertEquals(And('+(KSequence(5: K))), And('+(KSequence(divide(10, 2)))).normalize)
    assertEquals('+('+(KSequence(5: K)), '+(KMapAppLabel("Map")())), '+('+(KSequence(divide(10, 2))), '+(KMapAppLabel
      ("Map")())
    ).normalize)


  }

  @Test def AndMatcher {
    assertEquals(Or(And()), And().matcher(KToken(Sorts.Bool, "true", Att())).normalize)
    assertEquals(Or(And()), And().matcher(And()).normalize)
  }
}
