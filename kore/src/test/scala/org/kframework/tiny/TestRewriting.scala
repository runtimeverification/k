package org.kframework.tiny

import org.kframework.kore.KORE._
import org.kframework.kore._
import org.kframework.tiny.TrueAndFalse._
import org.kframework.tiny.builtin.KInt._

class TestRewriting {
  import org.junit._
  import org.kframework.tiny.Rewritable._

  implicit val theory = FreeTheory
  val X = KVariable("X")
  val Y = KVariable("Y")

  @Test
  def testSimple() {
    assertEquals(Set(5: K), (4: K).searchFor(KRewrite(4, 5)))
  }

  @Test
  def testSimpleWithFalseSideCondition() {
    assertEquals(Set(), (4: K).searchFor(KRewrite(4, 5), False))
  }

  @Test
  def testSimpleWithTrueSideCondition() {
    assertEquals(Set(5: K), (4: K).searchFor(KRewrite(4, 5), True))
  }

  @Test
  def testSimpleNoMatch() {
    assertEquals(Set(), (3: K).searchFor(KRewrite(4, 5)))
  }

  @Test
  def testSimpleApplyNoMatch() {
    assertEquals(Set(), 'foo(3).searchFor(KRewrite('foo(4), 'foo(5))))
  }

  @Test
  def testSimpleApply() {
    assertEquals(Set('foo(5)), 'foo(4).searchFor(KRewrite('foo(4), 'foo(5))))
  }

  @Test
  def testVar() {
    assertEquals(Set('foo(5)), 'foo(4).searchFor(KRewrite(X, 'foo(5))))
  }

  @Test
  def testVarInside() {
    assertEquals(Set('foo(5)), 'foo(4).searchFor(KRewrite('foo(X), 'foo(5))))
  }

  @Test
  def testVarSubstitution() {
    assertEquals(Set('foo(5, 4)), 'foo(4).searchFor(KRewrite('foo(X), 'foo(5, X))))
  }

  @Test
  def testVarSubstitutionWithTrueSideCondition() {
    assertEquals(Set('foo(5, 4)), 'foo(4).searchFor(KRewrite('foo(X), 'foo(5, X)), Equals(X, 4)))
  }

  @Test
  def testVarSubstitutionWithFalseSideCondition() {
    assertEquals(Set(), 'foo(4).searchFor(KRewrite('foo(X), 'foo(5, X)), Equals(X, 7)))
  }

  @Test
  def testVarSubstitution1() {
    assertEquals(Set('foo(5, 4, 5)),
      'foo(4, 5, 6).searchFor(KRewrite('foo(X, 6), 'foo(5, X))))
  }

  @Test
  def testVarSubstitution2() {
    assertEquals(Set('foo(5, 4, 5, 4, 5)), 'foo(4, 5, 6).searchFor(KRewrite('foo(X, 6), 'foo(5, X, X))))
  }

  @Test
  def testDeduplicate() {
    assertEquals(Set('foo(4, 4)), 'foo(4, 4, 4, 4).searchFor(KRewrite('foo(X, X), 'foo(X))))
  }

  @Test
  def testDeduplicateNot() {
    assertEquals(Set(), 'foo(4, 4, 4, 4, 4).searchFor(KRewrite('foo(X, X), 'foo(X))))
  }

  @Test
  def testKLabelMatch() {
    assertEquals(Set('foo(4)), 'foo(4, 4).searchFor(KRewrite(KApply(X, KList(4, 4)), KApply(X, KList(4)), Attributes())))
  }

  @Test
  def simple() {
    assertEquals(Set('foo(1, 3)),
      'foo(1, 2).searchFor(KRewrite('foo(1, 2), 'foo(1, 3))))
  }

  @Test
  def simpleSwap() {
    assertEquals(Set('foo(2, 1)),
      'foo(1, 2).searchFor(KRewrite('foo(X, Y), 'foo(Y, X)), Equals(X, 1)))
  }

  @Test @Ignore
  def simpleSwapOfId() {
    assertEquals(Set('foo(1, 1)),
      'foo(1, 1).searchFor(KRewrite('foo(X, Y), 'foo(Y, X)), Equals(X, Y)))
  }

  @Test def testSimpleToTerm {
    assertEquals(Set('foo(1, 3)),
      'foo(1, 2).searchFor('foo(1, KRewrite(2, 3))))
  }

  @Test def testWithVariableInside {
    assertEquals(Set('foo(1, 3)),
      'foo(1, 'bar(2, 3)).searchFor(KRewrite('foo(1, 'bar(2, X)), 'foo(1, X))))
  }

  @Test def testToTermWithVariableInside {
    assertEquals(Set('foo(1, 3)),
      'foo(1, 'bar(2, 3)).searchFor('foo(1, KRewrite('bar(2, X), X))))
  }

  @Test def testAnywhere {
    assertEquals(Set('bar('foo(0)), 'foo('bar(0))),
      'foo('bar('foo(0))).searchFor(Anywhere(KRewrite('foo(X), X))))
  }

  @Test def testTwoAnywheres {
    val o = 'foo('foo('foo('foo())))
    val inner = Anywhere('foo(KRewrite('foo(X), X)), "inner")
    val outer = Anywhere('foo(inner), "outer")

    assertEquals(Set('foo('foo('foo())),
      'foo('foo('foo('foo())))), o.searchFor(outer))
  }

  //  @Test def testRepeat {
  //    val o = 'foo('foo('foo('foo())))
  //    import Anywhere._
  //    val rep = Repeat(KRewrite('foo(X), X))
  //
  //    assertEquals(Set(), o.searchFor(rep))
  //  }

  def assertEquals(expected: Any, actual: Any) {
    if (expected != actual) {
      Assert.assertEquals(expected.toString(), actual.toString())
    }
  }

}
