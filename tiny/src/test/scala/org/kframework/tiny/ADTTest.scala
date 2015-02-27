package org.kframework.tiny

import org.junit.Test

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
  }
}
