package org.kframework.tiny

import org.kframework.kore._
import KORE._
import org.kframework.builtin.KInt._
import org.kframework.tiny.Anywhere

class TestRewriting {
  import org.junit._
  import Assert._

  val X = KVariable("X")

  @Test
  def testSimple() {
    assertEquals(Set(5: K), 4.search(KRewrite(4, 5)))
  }

  @Test
  def testSimpleNoMatch() {
    assertEquals(Set(), 3.search(KRewrite(4, 5)))
  }

  @Test
  def testSimpleApplyNoMatch() {
    assertEquals(Set(), 'foo(3).search(KRewrite('foo(4), 'foo(5))))
  }

  @Test
  def testSimpleApply() {
    assertEquals(Set('foo(5)), 'foo(4).search(KRewrite('foo(4), 'foo(5))))
  }

  @Test
  def testVar() {
    assertEquals(Set('foo(5)), 'foo(4).search(KRewrite(X, 'foo(5))))
  }

  @Test
  def testVarInside() {
    assertEquals(Set('foo(5)), 'foo(4).search(KRewrite('foo(X), 'foo(5))))
  }

  @Test
  def testVarSubstitution() {
    assertEquals(Set('foo(5, 4)), 'foo(4).search(KRewrite('foo(X), 'foo(5, X))))
  }

  @Test
  def testVarSubstitution1() {
    assertEquals(Set('foo(5, 4, 5)),
      'foo(4, 5, 6).search(KRewrite('foo(X, 6), 'foo(5, X))))
  }

  @Test
  def testVarSubstitution2() {
    assertEquals(Set('foo(5, 4, 5, 4, 5)), 'foo(4, 5, 6).search(KRewrite('foo(X, 6), 'foo(5, X, X))))
  }

  @Test
  def testDeduplicate() {
    assertEquals(Set('foo(4, 4)), 'foo(4, 4, 4, 4).search(KRewrite('foo(X, X), 'foo(X))))
  }

  @Test
  def testDeduplicateNot() {
    assertEquals(Set(), 'foo(4, 4, 4, 4, 4).search(KRewrite('foo(X, X), 'foo(X))))
  }

  @Test
  def testKLabelMatch() {
    assertEquals(Set('foo(4)), 'foo(4, 4).search(KRewrite(KApply(X, KList(4, 4)), KApply(X, KList(4)), Attributes())))
  }

  @Test
  def simple() {
    assertEquals(Set('foo(1, 3)),
      'foo(1, 2).search(KRewrite('foo(1, 2), 'foo(1, 3))))
  }

  @Test def testSimpleToTerm {
    assertEquals(Set('foo(1, 3)),
      'foo(1, 2).search('foo(1, KRewrite(2, 3))))
  }

  @Test def testWithVariableInside {
    assertEquals(Set('foo(1, 3)),
      'foo(1, 'bar(2, 3)).search(KRewrite('foo(1, 'bar(2, X)), 'foo(1, X))))
  }

  @Test def testToTermWithVariableInside {
    assertEquals(Set('foo(1, 3)),
      'foo(1, 'bar(2, 3)).search('foo(1, KRewrite('bar(2, X), X))))
  }

  @Test def testAnywhere {
    assertEquals(Set('bar('foo(0)), 'foo('bar(0))),
      'foo('bar('foo(0))).search(Anywhere(KRewrite('foo(X), X))))
  }

  def assertEquals(expected: Any, actual: Any) {
    if (expected != actual) {
      Assert.assertEquals(expected.toString(), actual.toString())
    }
  }

}
