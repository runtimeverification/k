package org.kframework.kore

import KORE._
import KInt._

class TestPatternMatching {
  import org.junit._
  import Assert._

  val X = KVariable("X")

  @Test
  def testSimple() {
    val foo = 'foo()
    assertEquals(Some(Map(X -> foo)), foo.m(X))
  }

  @Test
  def testEmptyMatch() {
    val foo = 'foo()
    assertEquals(Some(Map()), foo.m(foo))
  }

  @Test
  def testKApply() {
    val five = KToken(Sort("Int"), KString("5"))
    val foo = 'foo(five)
    val pattern = 'foo(X)
    assertEquals(Some(Map(X -> KList(five))), foo.m(pattern))
  }

  @Test
  def testKApply1() {
    val five = KToken(Sort("Int"), KString("5"))
    val foo = 'foo(five)
    val pattern = KApply(KLabel("bar"), Seq(X))
    assertEquals(None, foo.m(pattern))
  }

  @Test
  def testKListEntire() {
    val foo = 'foo(5, 6)
    val pattern = 'foo(X)
    assertEquals(Set(Map(X -> KList(5, 6))), foo.matchAll(pattern))
  }

  @Test
  def testKListPrefix() {
    val foo = 'foo(5, 6, 7)
    val pattern = 'foo(X, 7)
    assertEquals(Set(Map(X -> KList(5, 6))), foo.matchAll(pattern))
  }

  @Test
  def testKListPostfix() {
    val foo = 'foo(5, 6, 7)
    val pattern = 'foo(5, X)
    assertEquals(Set(Map(X -> KList(6, 7))), foo.matchAll(pattern))
  }

  @Test
  def testKListMiddle() {
    val foo = 'foo(5, 6, 7, 8)
    val pattern = 'foo(5, X, 8)
    assertEquals(Set(Map(X -> KList(6, 7))), foo.matchAll(pattern))
  }

  @Test
  def testKListAssoc() {
    val foo = 'foo(5)
    val Y = KVariable("Y")
    val pattern = 'foo(X, Y)
    assertEquals(Set(Map(X -> KList(), Y -> KList(5)), Map(X -> KList(5), Y -> KList())), foo.matchAll(pattern))
  }

  @Test
  def testKListAssoc1() {
    val foo = 'foo(5, 6)
    val Y = KVariable("Y")
    val pattern = 'foo(X, Y)
    assertEquals(Set(Map(X -> KList(), Y -> KList(5, 6)), Map(X -> KList(5), Y -> KList(6)), Map(X -> KList(5, 6), Y -> KList())),
      foo.matchAll(pattern))
  }

  @Test
  def testKListAssoc2() {
    val foo = 'foo(5, 7, 6)
    val Y = KVariable("Y")
    val pattern = 'foo(X, 7, Y)
    assertEquals(Set(Map(X -> KList(5), Y -> KList(6))),
      foo.matchAll(pattern))
  }

  @Test
  def testKListAssoc3() {
    val foo = 'foo(5, 5, 5)
    val Y = KVariable("Y")
    val pattern = 'foo(X, 5, Y)
    assertEquals(Set(Map(X -> KList(), Y -> KList(5, 5)), Map(X -> KList(5), Y -> KList(5)), Map(X -> KList(5, 5), Y -> KList())),
      foo.matchAll(pattern))
  }

  @Test
  def testKListMultipleVar() {
    val foo = 'foo(5, 5)
    val pattern = 'foo(X, X)
    assertEquals(Set(Map(X -> KList(5))),
      foo.matchAll(pattern))
  }

  @Test
  def testKListAssocMultipleVar() {
    val foo = 'foo(5, 5, 5)
    val pattern = 'foo(X, X)
    assertEquals(Set(),
      foo.matchAll(pattern))
  }

  @Test
  def testKApplyWithEmptySeq() {
    val foo = 'foo()
    val pattern = 'foo(X)
    assertEquals(Some(Map(X -> KList())), foo.m(pattern))
  }

  @Test
  def testKVariableMatchingKLabel() {
    val foo = 'foo()
    val pattern = KApply(X, Seq(), Attributes())
    assertEquals(Some(Map(X -> MetaKLabel('foo))), foo.m(pattern))
  }

  @Test
  def testKSeqAssoc() {
    val foo = KSequence(5, 5, 5)
    val Y = KVariable("Y")
    val pattern = KSequence(X, 5, Y)
    assertEquals(Set(Map(X -> KSequence(), Y -> KSequence(5, 5)), Map(X -> KSequence(5), Y -> KSequence(5)), Map(X -> KSequence(5, 5), Y -> KSequence())),
      foo.matchAll(pattern))
  }

  @Test
  def testAttributes() {
    val foo = 'foo()
    assertEquals(Some(Map(X -> foo)), foo.m(X))
  }

  def assertEquals(expected: Any, actual: Any) {
    if (expected != actual) {
      Assert.assertEquals(expected.toString(), actual.toString())
    }
  }

}
