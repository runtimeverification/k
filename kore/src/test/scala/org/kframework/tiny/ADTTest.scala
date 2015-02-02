package org.kframework.tiny

import org.junit.Test
import org.junit.Assert._
import org.kframework.attributes.Att
import org.kframework.definition.Module

class ADTTest {
  val cons = new Constructors(Module("TEST", Set(), Set(), Att()))

  import cons._

  val KInt = Sort("Int")
  val KString = Sort("String")

  implicit def stringToToken(s: String) = KToken(KString, s, Att())
  implicit def symbolToLabel(l: Symbol) = KLabel(l.toString())
  implicit def intToToken(n: Int): K = KToken(KInt, n.toString, Att())
  implicit def KWithSeq(k: K) = new {
    def ~>(other: K) = KSeq(Seq(k, other), Att())
    def ==>(other: K) = KRewrite(k, other, Att())
  }

  val X = KVar("X")

  val seqX2 = X ~> 2
  val foo = 'foo()
  val rew = (1: K) ==> 2

  @Test def equalities {
    assertEquals(2: K, 2: K)
    assertEquals(X, KVar("X"))
    assertEquals(seqX2, X ~> 2)
    assertNotEquals(seqX2, X ~> X ~> 2)
    assertEquals(KSeq(X, X, 2), KSeq(X, KSeq(X, 2)))
    assertEquals(KSeq(X, X, 2), KSeq(KSeq(X, X), 2))
    assertEquals(foo, RegularKAppLabel("foo", Att())())
    assertNotEquals(foo, RegularKAppLabel("foo foo", Att())())
    assertNotEquals(foo, RegularKAppLabel("foo", Att())(X))
  }
}
