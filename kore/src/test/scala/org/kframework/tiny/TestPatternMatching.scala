package org.kframework.tiny

import org.kframework.kore._
import KORE._
import org.kframework.tiny.builtin.KInt._

class TestPatternMatching {
  import org.junit._
  import Assert._

  val X = KVariable("X")

  @Test def testSimple() {
    val foo = 'foo()
    assertEquals(Some(Map(X -> foo)), X.matchOne(foo))
  }

  @Test def testEmptyMatch() {
    val foo = 'foo()
    assertEquals(Some(Map()), foo.matchOne(foo))
  }

  @Test def testKApply() {
    val foo = 'foo(5)
    val pattern = 'foo(X)
    assertEquals(Some(Map(X -> 5)), pattern.matchOne(foo))
  }

  @Test def testKApply1() {
    val five = KToken(Sort("Int"), "5")
    val foo = 'foo(five)
    val pattern = KApply(KLabel("bar"), Seq(X))
    assertEquals(None, pattern.matchOne(foo))
  }

  @Test def testNested() {
    assertEquals(Set(Map(X -> (5: K))), 'foo('bar(X)).matchAll('foo('bar(5))))
  }

  @Test def testKListEntire() {
    val foo = 'foo(5, 6)
    val pattern = 'foo(X)
    assertEquals(Set(Map(X -> KList(5, 6))), pattern.matchAll(foo))
  }

  @Test def testKListPrefix() {
    val foo = 'foo(5, 6, 7)
    val pattern = 'foo(X, 7)
    assertEquals(Set(Map(X -> KList(5, 6))), pattern.matchAll(foo))
  }

  @Test def testKListPostfix() {
    val foo = 'foo(5, 6, 7)
    val pattern = 'foo(5, X)
    assertEquals(Set(Map(X -> KList(6, 7))), pattern.matchAll(foo))
  }

  @Test def testKListMiddle() {
    val foo = 'foo(5, 6, 7, 8)
    val pattern = 'foo(5, X, 8)
    assertEquals(Set(Map(X -> KList(6, 7))), pattern.matchAll(foo))
  }

  @Test def testKListAssoc() {
    val foo = 'foo(5)
    val Y = KVariable("Y")
    val pattern = 'foo(X, Y)
    assertEquals(Set(Map(X -> KList(), Y -> 5), Map(X -> 5, Y -> KList())), pattern.matchAll(foo))
  }

  @Test def testKListAssoc1() {
    val foo = 'foo(5, 6)
    val Y = KVariable("Y")
    val pattern = 'foo(X, Y)
    assertEquals(Set(Map(X -> KList(), Y -> KList(5, 6)), Map(X -> 5, Y -> 6), Map(X -> KList(5, 6), Y -> KList())),
      pattern.matchAll(foo))
  }

  @Test def testKListAssoc2() {
    val foo = 'foo(5, 7, 6)
    val Y = KVariable("Y")
    val pattern = 'foo(X, 7, Y)
    assertEquals(Set(Map(X -> 5, Y -> 6)),
      pattern.matchAll(foo))
  }

  @Test def testKListAssoc3() {
    val foo = 'foo(5, 5, 5)
    val Y = KVariable("Y")
    val pattern = 'foo(X, 5, Y)
    assertEquals(Set(Map(X -> KList(), Y -> KList(5, 5)), Map(X -> 5, Y -> 5), Map(X -> KList(5, 5), Y -> KList())),
      pattern.matchAll(foo))
  }

  @Test def testKListMultipleVar() {
    val foo = 'foo(5, 5)
    val pattern = 'foo(X, X)
    assertEquals(Set(Map(X -> (5: K))),
      pattern.matchAll(foo))
  }

  @Test def testKListAssocMultipleVar() {
    val foo = 'foo(5, 5, 5)
    val pattern = 'foo(X, X)
    assertEquals(Set(),
      pattern.matchAll(foo))
  }

  @Test def testKApplyWithEmptySeq() {
    val foo = 'foo()
    val pattern = 'foo(X)
    assertEquals(Some(Map(X -> KList())), pattern.matchOne(foo))
  }

  @Test def testKVariableMatchingKLabel() {
    val foo = 'foo()
    val pattern = KApply(X, Seq(), Attributes())
    assertEquals(Some(Map(X -> MetaKLabel('foo))), pattern.matchOne(foo))
  }

  @Test def testKSeqAssoc() {
    val foo = KSequence(5, 5, 5)
    val Y = KVariable("Y")
    val pattern = KSequence(X, 5, Y)
    assertEquals(Set(Map(X -> KSequence(), Y -> KSequence(5, 5)), Map(X -> KSequence(5), Y -> KSequence(5)), Map(X -> KSequence(5, 5), Y -> KSequence())),
      pattern.matchAll(foo))
  }

  @Test def testAttributes() {
    val foo = 'foo()
    assertEquals(Some(Map(X -> foo)), X.matchOne(foo))
  }

  @Test def testAnywhere() {
    val o = 'foo('bar('foo()))
    import Anywhere._
    val a = Anywhere('foo(X))
    assertEquals(
      Set(Map(X -> 'bar('foo()), a.TOPVariable -> a.HOLEVariable),
        Map(X -> KSequence(), a.TOPVariable -> 'foo('bar(a.HOLEVariable)))),
      a.matchAll(o))
  }

  @Test def testTwoAnywheres() {
    val o = 'foo('foo('foo()))
    import Anywhere._
    val inner = Anywhere('foo(X), "inner")
    val outer = Anywhere('foo(inner), "outer")
    println(outer)
    assertEquals(
      Set(Map(X -> 'foo(), inner.TOPVariable -> inner.HOLEVariable, outer.TOPVariable -> outer.HOLEVariable),
        Map(X -> KSequence(), inner.TOPVariable -> 'foo(inner.HOLEVariable), outer.TOPVariable -> outer.HOLEVariable),
        Map(X -> KSequence(), inner.TOPVariable -> inner.HOLEVariable, outer.TOPVariable -> 'foo(outer.HOLEVariable))),
      outer.matchAll(o))
  }

  def assertEquals(expected: Any, actual: Any) {
    if (expected != actual) {
      Assert.assertEquals(expected.toString(), actual.toString())
    }
  }

}
