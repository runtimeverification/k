package org.kframework.tiny

import org.junit.Test
import org.junit.Assert._
import org.kframework.attributes.Att

class ADTTest {
  implicit val t = FreeTheory

  val X = KVar("X")
  val KInt = Sort("Int")
  val one = KTok(KInt, "1")
  val two = KTok(KInt, "2")
  val two1 = KTok(KInt, "2")
  val seqX2 = KSeq(X, two)
  val foo = RegularKAppLabel("foo", Att())()
  val rew = KRewrite(one, two)

  @Test def equalities {
    assertEquals(KTok(KInt, "2"), two)
    assertEquals(X, KVar("X"))
    assertEquals(seqX2, KSeq(X, two))
    assertNotEquals(seqX2, KSeq(X, X, two))
    assertEquals(KSeq(X, X, two), KSeq(X, KSeq(X, two)))
    assertEquals(KSeq(X, X, two), KSeq(KSeq(X, X), two))
    assertEquals(foo, RegularKAppLabel("foo", Att())())
    assertNotEquals(foo, RegularKAppLabel("foo foo", Att())())
    assertNotEquals(foo, RegularKAppLabel("foo", Att())(X))
  }
}
