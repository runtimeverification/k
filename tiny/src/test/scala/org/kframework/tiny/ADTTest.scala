package org.kframework.tiny

import org.junit.Test
import org.kframework.builtin.Sorts
import org.kframework.tiny.builtin.KMapAppLabel

class ADTTest extends AbstractTest {

  import cons._

  val seqX2 = X ~> 2
  val rew = (1: K) ==> 2


  @Test def equalities {
    assertEquals(2: K, 2: K)
    assertEquals(X, KVar("X"))
    assertEquals(seqX2, X ~> 2)
    assertNotEquals(seqX2, X ~> X ~> 2)
    assertEquals(KSeq(X, X, 2), KSeq(X, KSeq(X, 2)))
    assertEquals(KSeq(X, X, 2), KSeq(KSeq(X, X), 2))
    assertEquals('foo(), RegularKAppLabel("foo", Att())())
    assertNotEquals('foo(), RegularKAppLabel("foo foo", Att())())
    assertNotEquals('foo(), RegularKAppLabel("foo", Att())(X))

    val divide = NativeBinaryOpLabel("/", Att(), (x: Int, y: Int) => x / y, Sorts.Int)

    assertEquals(5: K, divide(10, 2).normalize)
    assertEquals(KSeq(5: K), KSeq(divide(10, 2)).normalize)
    assertEquals('foo(KSeq(5: K)), 'foo(KSeq(divide(10, 2))).normalize)
    assertEquals(And('foo(KSeq(5: K))), And('foo(divide(10, 2))).normalize)
    assertEquals(And('+(KSeq(5: K))), And('+(KSeq(divide(10, 2)))).normalize)
    assertEquals('+('+(KSeq(5: K)), '+(KMapAppLabel("Map")())), '+('+(KSeq(divide(10, 2))), '+(KMapAppLabel("Map")())
    ).normalize)


  }

  @Test def AndMatcher {
    assertEquals(And(), KToken(Sorts.Bool, "true", Att()).matcher(And()).normalize)
    assertEquals(Or(And()), And().matcher(And()).normalize)
  }
}
