package org.kframework.tiny

import org.junit.{Assert, Ignore, Test}
import org.kframework.attributes._
import org.kframework.tiny.matcher.Anywhere

class TestRewriting extends AbstractTest {

  import cons._

  implicit class KToRewriting(self: K) {
    def searchFor(rewrite: K, sideConditions: K = True)(implicit theory: Theory): Set[K] = {
      Rule(rewrite, sideConditions)(theory)(self)
    }
  }

  @Test
  def testSimple() {
    assertEquals(Set(5: K), (4: K).searchFor((4: K) ==> 5: K))
  }

  @Test
  def testSimpleWithFalseSideCondition() {
    assertEquals(Set(), (4: K).searchFor((4: K) ==> 5: K, False))
  }

  @Test
  def testSimpleWithTrueSideCondition() {
    assertEquals(Set(5: K), (4: K).searchFor((4: K) ==> 5: K, True))
  }

  @Test
  def testSimpleNoMatch() {
    assertEquals(Set(), (3: K).searchFor((4: K) ==> 5: K))
  }

  @Test
  def testSimpleApplyNoMatch() {
    assertEquals(Set(), 'foo(3).searchFor('foo(4) ==> 'foo(5)))
  }

  @Test
  def testSimpleApply() {
    assertEquals(Set('foo(5)), 'foo(4).searchFor('foo(4) ==> 'foo(5)))
  }

  @Test
  def testVar() {
    assertEquals(Set('foo(5)), 'foo(4).searchFor(X ==> 'foo(5)))
  }

  @Test
  def testVarInside() {
    assertEquals(Set('foo(5)), 'foo(4).searchFor('foo(X) ==> 'foo(5)))
  }

  @Test
  def testVarSubstitution() {
    assertEquals(Set('foo(5, 4)), 'foo(4).searchFor('foo(X) ==> 'foo(5, X)))
  }

  @Test
  def testVarSubstitutionWithTrueSideCondition() {
    assertEquals(Set('foo(5, 4)), 'foo(4).searchFor('foo(X) ==> 'foo(5: K, X), Equals(X, 4)))
  }

  @Test
  def testVarSubstitutionWithFalseSideCondition() {
    assertEquals(Set(), 'foo(4).searchFor('foo(X) ==> 'foo(5, X), Equals(X, 7)))
  }

  @Test
  def testVarSubstitution1() {
    assertEquals(Set((5: K) + 4 + 5),
      ((4: K) + 5 + 6).searchFor(X + 6 ==> (5: K) + X))
  }

  @Test
  def testVarSubstitution2() {
    assertEquals(Set('+(5, 4, 5, 4, 5)), '+(4, 5, 6).searchFor('+(X, 6) ==> '+(5, X, X)))
  }

  @Test
  def testDeduplicate() {
    assertEquals(Set('+(4, 4)), '+(4, 4, 4, 4).searchFor('+(X, X) ==> '+(X)))
  }

  @Test
  def testDeduplicateNot() {
    assertEquals(Set(), '+(4, 4, 4, 4, 4).searchFor('+(X, X) ==> '+(X)))
  }

  @Test @Ignore
  def testKLabelMatch() {
    assertEquals(Set('foo(4)), 'foo(4, 4).searchFor(KApply(X, List(4: K, 4: K)) ==> KApply(X, List(4: K), Att
      ())))
  }

  @Test
  def simple() {
    assertEquals(Set('foo(1, 3)),
      'foo(1, 2).searchFor('foo(1, 2) ==> 'foo(1, 3)))
  }

  @Test
  def simpleSwap() {
    assertEquals(Set('foo(2, 1)),
      'foo(1, 2).searchFor('foo(X, Y) ==> 'foo(Y, X), Equals(X, 1)))
  }

  @Test
  @Ignore
  def simpleSwapOfId() {
    assertEquals(Set('foo(1, 1)),
      'foo(1, 1).searchFor('foo(X, Y) ==> 'foo(Y, X), Equals(X, Y)))
  }

  @Test def testSimpleToTerm {
    assertEquals(Set('foo(1, 3)),
      'foo(1, 2).searchFor('foo(1, (2: K) ==> 3)))
  }

  @Test def testWithVariableInside {
    assertEquals(Set('foo(1, 3)),
      'foo(1, 'bar(2, 3)).searchFor('foo(1, 'bar(2, X)) ==> 'foo(1, X)))
  }

  @Test def testToTermWithVariableInside {
    assertEquals(Set('foo(1, 3)),
      'foo(1, 'bar(2, 3)).searchFor('foo(1, 'bar(2, X) ==> X)))
  }

  @Test def testAnywhere {
    assertEquals(Set('bar('foo(0)), 'foo('bar(0))),
      'foo('bar('foo(0))).searchFor(Anywhere("ONE", 'foo(X) ==> X)))
  }

  @Test
  @Ignore def testTwoAnywheres {
    val o = 'foo('foo('foo('foo())))
    val inner = Anywhere("inner", 'foo('foo(X)) ==> X)
    val outer = Anywhere("outer", 'foo(inner))

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
