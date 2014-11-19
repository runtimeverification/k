package org.kframework.kore

import KORE._
import KInt._

class TestPatternMatching {
  import org.junit._
  import Assert._

  @Test
  def testSimple() {
    val foo = KApply(KLabel("foo"), KList())
    val v = KVariable("X")
    assertEquals(Some(Map(v -> foo)), foo.m(v))
  }

  @Test
  def testEmptyMatch() {
    val foo = KApply(KLabel("foo"), KList())
    assertEquals(Some(Map()), foo.m(foo))
  }

  @Test
  def testKApply() {
    val five = KToken(Sort("Int"), KString("5"))
    val foo = KApply(KLabel("foo"), KList(five))
    val v = KVariable("X")
    val pattern = KApply(KLabel("foo"), KList(v))
    assertEquals(Some(Map(v -> 'klist(five))), foo.m(pattern))
  }

  @Test
  def testKApply1() {
    val five = KToken(Sort("Int"), KString("5"))
    val foo = KApply(KLabel("foo"), KList(five))
    val v = KVariable("X")
    val pattern = KApply(KLabel("bar"), KList(v))
    assertEquals(None, foo.m(pattern))
  }

  @Test
  def testKListEntire() {
    val foo = KApply(KLabel("foo"), KList(5, 6))
    val v = KVariable("X")
    val pattern = KApply(KLabel("foo"), KList(v))
    assertEquals(Set(Map(v -> 'klist(5, 6))), foo.matchAll(pattern))
  }

  @Test
  def testKListPrefix() {
    val foo = KApply(KLabel("foo"), KList(5, 6, 7))
    val v = KVariable("X")
    val pattern = KApply(KLabel("foo"), KList(v, 7))
    assertEquals(Set(Map(v -> 'klist(5, 6))), foo.matchAll(pattern))
  }

  @Test
  def testKListPostfix() {
    val foo = KApply(KLabel("foo"), KList(5, 6, 7))
    val v = KVariable("X")
    val pattern = KApply(KLabel("foo"), KList(5, v))
    assertEquals(Set(Map(v -> 'klist(6, 7))), foo.matchAll(pattern))
  }

  @Test
  def testKListMiddle() {
    val foo = KApply(KLabel("foo"), KList(5, 6, 7, 8))
    val v = KVariable("X")
    val pattern = KApply(KLabel("foo"), KList(5, v, 8))
    assertEquals(Set(Map(v -> 'klist(6, 7))), foo.matchAll(pattern))
  }

  @Test
  def testKListAssoc() {
    val foo = KApply(KLabel("foo"), KList(5))
    val X = KVariable("X")
    val Y = KVariable("Y")
    val pattern = KApply(KLabel("foo"), KList(X, Y))
    assertEquals(Set(Map(X -> KList(), Y -> KList(5)), Map(X -> KList(5), Y -> KList())), foo.matchAll(pattern))
  }

  @Test
  def testKListAssoc1() {
    val foo = KApply(KLabel("foo"), KList(5, 6))
    val X = KVariable("X")
    val Y = KVariable("Y")
    val pattern = KApply(KLabel("foo"), KList(X, Y))
    assertEquals(Set(Map(X -> KList(), Y -> KList(5, 6)), Map(X -> KList(5), Y -> KList(6)), Map(X -> KList(5, 6), Y -> KList())),
      foo.matchAll(pattern))
  }

  @Test
  def testKListAssoc2() {
    val foo = KApply(KLabel("foo"), KList(5, 7, 6))
    val X = KVariable("X")
    val Y = KVariable("Y")
    val pattern = KApply(KLabel("foo"), KList(X, 7, Y))
    assertEquals(Set(Map(X -> KList(5), Y -> KList(6))),
      foo.matchAll(pattern))
  }

  @Test
  def testKListAssoc3() {
    val foo = KApply(KLabel("foo"), KList(5, 5, 5))
    val X = KVariable("X")
    val Y = KVariable("Y")
    val pattern = KApply(KLabel("foo"), KList(X, 5, Y))
    assertEquals(Set(Map(X -> KList(), Y -> KList(5, 5)), Map(X -> KList(5), Y -> KList(5)), Map(X -> KList(5, 5), Y -> KList())),
      foo.matchAll(pattern))
  }

  @Test
  def testKApplyWithEmptySeq() {
    val foo = KApply(KLabel("foo"), KList())
    val v = KVariable("X")
    val pattern = KApply(KLabel("foo"), KList(v))
    assertEquals(Some(Map(v -> KSequence())), foo.m(pattern))
  }

  def assertEquals(expected: Any, actual: Any) {
    if (expected != actual) {
      Assert.assertEquals(expected.toString(), actual.toString())
    }
  }

}
