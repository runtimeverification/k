package org.kframework.tiny

import org.junit.Test
import org.junit.Assert
import org.kframework.attributes.Att
import org.kframework.definition.{Production, Module}
import org.kframework.kore.{Unparse, ADT}

class ADTTest {

  val KInt = ADT.Sort("Int")

  val KString = ADT.Sort("String")

  val cons = new Constructors(Module("TEST", Set(), Set(
    Production(ADT.KLabel("foo"), KString, Seq(), Att())
  ), Att()))

  import cons._

  implicit def stringToToken(s: String) = KToken(KString, s, Att())
  implicit def symbolToLabel(l: Symbol) = KLabel(l.name)
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

  def assertEquals(k1: K, k2: K) {
    if (k1 != k2)
      Assert.assertEquals(Unparse(k1), Unparse(k2))
  }

  def assertNotEquals(k1: K, k2: K): Unit = {
    if (k1 == k2)
      Assert.assertNotEquals(Unparse(k1), Unparse(k2))
  }
}
