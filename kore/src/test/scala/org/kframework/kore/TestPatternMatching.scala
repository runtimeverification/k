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
    assertEquals(Some(Map(v -> five)), foo.m(pattern))
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
  def testAssoc() {
    val foo = KApply(KLabel("foo"), KList(5, 6))
    val v = KVariable("X")
    val pattern = KApply(KLabel("foo"), KList(v))
    assertEquals(Map(v -> (5: K)), foo.m(pattern))
  }

  // will deal with it after figuring out the multiplicity of a variable
  @Test @Ignore
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
