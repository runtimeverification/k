package org.kframework.kore

import KORE._
import KInt._

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
    assertEquals(Set('foo(5, 4, 5)), 'foo(4, 5, 6).search(KRewrite('foo(X, 6), 'foo(5, X))))
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

  def assertEquals(expected: Any, actual: Any) {
    if (expected != actual) {
      Assert.assertEquals(expected.toString(), actual.toString())
    }
  }

}
