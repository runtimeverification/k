package org.kframework.tiny

import org.kframework.kore._
import KORE._
import org.kframework.tiny.builtin.KInt._

class TestPatternMatching {
  import org.junit._
  import Assert._

  val X = KVariable("X")

  implicit val equiv: Equivalence = EqualsEquivalence
  implicit val disj: Disjunction = new Disjunction(Set(Conjunction()))

  @Test def testSimple() {
    val foo = 'foo()
    assertEquals(Some(Conjunction(X -> foo)), X.matchOne(foo))
  }

  @Test def testEmptyMatch() {
    val foo = 'foo()
    assertEquals(Some(Conjunction()), foo.matchOne(foo))
  }

  @Test def testKApply() {
    val foo = 'foo((5: K))
    val pattern = 'foo(X)
    assertEquals(Some(Conjunction(X -> ((5: K): K))), pattern.matchOne(foo))
  }

  @Test def testKApply1() {
    val five = KToken(Sort("Int"), "(5:K)")
    val foo = 'foo(five)
    val pattern = KApply(KLabel("bar"), Seq(X))
    assertEquals(None, pattern.matchOne(foo))
  }

  @Test def testNested() {
    assertEquals(Disjunction(Conjunction(X -> ((5: K): K))), 'foo('bar(X)).matchAll('foo('bar((5: K)))))
  }

  @Test def testKListEntire() {
    val foo = 'foo((5: K), 6)
    val pattern = 'foo(X)
    assertEquals(Disjunction(Conjunction(X -> KList((5: K), 6))), pattern.matchAll(foo))
  }

  @Test def testKListPrefix() {
    val foo = 'foo((5: K), 6, 7)
    val pattern = 'foo(X, 7)
    assertEquals(Disjunction(Conjunction(X -> KList((5: K), 6))), pattern.matchAll(foo))
  }

  @Test def testKListPostfix() {
    val foo = 'foo((5: K), 6, 7)
    val pattern = 'foo((5: K), X)
    assertEquals(Disjunction(Conjunction(X -> KList(6, 7))), pattern.matchAll(foo))
  }

  @Test def testKListMiddle() {
    val foo = 'foo((5: K), 6, 7, 8)
    val pattern = 'foo((5: K), X, 8)
    assertEquals(Disjunction(Conjunction(X -> KList(6, 7))), pattern.matchAll(foo))
  }

  @Test def testKListAssoc() {
    val foo = 'foo((5: K))
    val Y = KVariable("Y")
    val pattern = 'foo(X, Y)
    assertEquals(Disjunction(Conjunction(X -> KList(), Y -> (5: K)), Conjunction(X -> (5: K), Y -> KList())), pattern.matchAll(foo))
  }

  @Test def testKListAssoc1() {
    val foo = 'foo((5: K), 6)
    val Y = KVariable("Y")
    val pattern = 'foo(X, Y)
    assertEquals(Disjunction(Conjunction(X -> KList(), Y -> KList((5: K), 6)), Conjunction(X -> (5: K), Y -> (6: K)), Conjunction(X -> KList((5: K), 6), Y -> KList())),
      pattern.matchAll(foo))
  }

  @Test def testKListAssoc2() {
    val foo = 'foo((5: K), 7, 6)
    val Y = KVariable("Y")
    val pattern = 'foo(X, 7, Y)
    assertEquals(Disjunction(Conjunction(X -> (5: K), Y -> (6: K))),
      pattern.matchAll(foo))
  }

  @Test def testKListAssoc3() {
    val foo = 'foo((5: K), (5: K), (5: K))
    val Y = KVariable("Y")
    val pattern = 'foo(X, (5: K), Y)
    assertEquals(Disjunction(Conjunction(X -> KList(), Y -> KList((5: K), (5: K))), Conjunction(X -> (5: K), Y -> (5: K)), Conjunction(X -> KList((5: K), (5: K)), Y -> KList())),
      pattern.matchAll(foo))
  }

  @Test def testKListMultipleVar() {
    val foo = 'foo((5: K), (5: K))
    val pattern = 'foo(X, X)
    assertEquals(Disjunction(Conjunction(X -> ((5: K): K))),
      pattern.matchAll(foo))
  }

  @Test def testKListAssocMultipleVar() {
    val foo = 'foo((5: K), (5: K), (5: K))
    val pattern = 'foo(X, X)
    assertEquals(Disjunction(), pattern.matchAll(foo))
  }

  @Test def testKApplyWithEmptySeq() {
    val foo = 'foo()
    val pattern = 'foo(X)
    assertEquals(Some(Conjunction(X -> KList())), pattern.matchOne(foo))
  }

  @Test def testKVariableMatchingKLabel() {
    val foo = 'foo()
    val pattern = KApply(X, Seq(), Attributes())
    assertEquals(Some(Conjunction(X -> MetaKLabel('foo))), pattern.matchOne(foo))
  }

  @Test def testKSeqAssoc() {
    val foo = KSequence((5: K), (5: K), (5: K))
    val Y = KVariable("Y")
    val pattern = KSequence(X, (5: K), Y)
    assertEquals(Disjunction(Conjunction(X -> KSequence(), Y -> KSequence((5: K), (5: K))), Conjunction(X -> KSequence((5: K)), Y -> KSequence((5: K))), Conjunction(X -> KSequence((5: K), (5: K)), Y -> KSequence())),
      pattern.matchAll(foo))
  }

  @Test def testAttributes() {
    val foo = 'foo()
    assertEquals(Some(Conjunction(X -> foo)), X.matchOne(foo))
  }

  @Test def testAnywhere() {
    val o = 'foo('bar('foo()))
    import Anywhere._
    val a = Anywhere('foo(X))
    assertEquals(
      Disjunction(Conjunction(X -> 'bar('foo()), a.TOPVariable -> a.HOLEVariable),
        Conjunction(X -> KSequence(), a.TOPVariable -> 'foo('bar(a.HOLEVariable)))),
      a.matchAll(o))
  }

  @Test def testTwoAnywheres() {
    val o = 'foo('foo('foo()))
    import Anywhere._
    val inner = Anywhere('foo(X), "inner")
    val outer = Anywhere('foo(inner), "outer")
    println(outer)
    assertEquals(
      Disjunction(Conjunction(X -> 'foo(), inner.TOPVariable -> inner.HOLEVariable, outer.TOPVariable -> outer.HOLEVariable),
        Conjunction(X -> KSequence(), inner.TOPVariable -> 'foo(inner.HOLEVariable), outer.TOPVariable -> outer.HOLEVariable),
        Conjunction(X -> KSequence(), inner.TOPVariable -> inner.HOLEVariable, outer.TOPVariable -> 'foo(outer.HOLEVariable))),
      outer.matchAll(o))
  }

  def assertEquals(expected: Any, actual: Any) {
    if (expected != actual) {
      Assert.assertEquals(expected.toString(), actual.toString())
    }
  }

}
