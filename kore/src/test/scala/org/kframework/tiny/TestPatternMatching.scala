package org.kframework.tiny

import org.junit.{Assert, Test}

class TestPatternMatching extends AbstractTest {

  import cons._

  implicit class KWithMatcherMethods(k: K) {
    def matchAll(other: K, sideConditions: K): Set[K] = theory.deepNormalize(And(k.matcher(other), sideConditions)) match {
      case or: Or => or.children
      case k => Set(k)
    }
    def matchOne(other: K, sideConditions: K) = matchAll(other, sideConditions).head
  }


  @Test def testSimple() {
    assertEquals(X -> 'foo(), theory.deepNormalize(X.matcher('foo())))
  }

  @Test def testSimpleWithFalseSideCondition() {
    val foo = 'foo()

    println(And(X.matcher('foo())))

    assertEquals(False, theory.deepNormalize(And(X.matcher('foo()), False)))
  }

  @Test def testSimpleWithTrueSideCondition() {
    val foo = 'foo()
    Assert.assertEquals(Set(And(X -> 'foo())), X.matchAll(foo, True))
  }

  @Test def testEmptyMatch() {
    val foo = 'foo()
    Assert.assertEquals(True, foo.matchOne(foo, True))
  }

  @Test def testKApply() {
    val foo = 'foo(5: K)
    val pattern = 'foo(X)
    Assert.assertEquals(And(X -> ((5: K): K)),
      pattern.matchOne(foo, True))
  }
  //
  //  @Test def testKApplyWithCondition() {
  //    val foo = 'foo(5: K)
  //    val pattern = 'foo(X)
  //    assertEquals(Some(And(X -> ((5: K): K))), pattern.matchOne(foo, Equals(X, 5: K)))
  //  }
  //
  //  @Test def testKApplyWithFailingCondition() {
  //    val foo = 'foo(5: K)
  //    val pattern = 'foo(X)
  //    assertEquals(False, pattern.matchAll(foo, Equals(X, 4: K)))
  //  }
  //
  //  @Test
  //  @Ignore def testKApplyIdWithFailingCondition() {
  //    val foo = 'foo(5: K, 6: K)
  //    val pattern = 'foo(X, Y)
  //    assertEquals(False, pattern.matchAll(foo, Equals(X, Y)))
  //  }
  //
  //  @Test
  //  @Ignore def testKApplyIdWithPassingCondition() {
  //    val foo = 'foo(5: K, 5: K)
  //    val pattern = 'foo(X, Y)
  //    assertEquals(Or(And(X -> (5: K), Y -> (5: K))), pattern.matchAll(foo, Equals(X, Y)))
  //  }
  //
  //  @Test def testKApply1() {
  //    val five = KToken(Sort("Int"), "(5:K)")
  //    val foo = 'foo(five)
  //    val pattern = KApply(KLabel("bar"), Seq(X))
  //    assertEquals(None, pattern.matchOne(foo))
  //  }
  //
  //  @Test def testNested() {
  //    assertEquals(Or(And(X -> ((5: K): K))), 'foo('bar(X)).matchAll('foo('bar(5: K))))
  //  }
  //
  //  @Test def testKListEntire() {
  //    val foo = 'foo(5: K, 6)
  //    val pattern = 'foo(X)
  //    assertEquals(Or(And(X -> KList(5: K, 6))), pattern.matchAll(foo))
  //  }
  //
  //  @Test def testKListPrefix() {
  //    val foo = 'foo(5: K, 6, 7)
  //    val pattern = 'foo(X, 7)
  //    assertEquals(Or(And(X -> KList(5: K, 6))), pattern.matchAll(foo))
  //  }
  //
  //  @Test def testKListPostfix() {
  //    val foo = 'foo(5: K, 6, 7)
  //    val pattern = 'foo(5: K, X)
  //    assertEquals(Or(And(X -> KList(6, 7))), pattern.matchAll(foo))
  //  }
  //
  //  @Test def testKListMiddle() {
  //    val foo = 'foo(5: K, 6, 7, 8)
  //    val pattern = 'foo(5: K, X, 8)
  //    assertEquals(Or(And(X -> KList(6, 7))), pattern.matchAll(foo))
  //  }
  //
  //  @Test def testKListAssoc() {
  //    val foo = 'foo(5: K)
  //
  //    val pattern = 'foo(X, Y)
  //    assertEquals(Or(And(X -> KList(), Y -> (5: K)), And(X -> (5: K), Y -> KList())), pattern.matchAll(foo))
  //  }
  //
  //  @Test def testKBagDifferentKLabel() {
  //    import org.kframework.koreimplementation
  //
  //    val foo = KBag(KLabel("foo"), koreimplementation.KList(1, 2, 3))
  //
  //    val pattern = KBag(KLabel("bar"), koreimplementation.KList(1, 2, 3))
  //    assertEquals(False, pattern.matchAll(foo))
  //  }
  //
  //  @Test def testKBagId() {
  //    import org.kframework.koreimplementation
  //
  //    val foo = KBag(KLabel("foo"), koreimplementation.KList(1, 2, 3))
  //
  //    val pattern = KBag(KLabel("foo"), koreimplementation.KList(1, 2, 3))
  //    assertEquals(Or(True), pattern.matchAll(foo))
  //  }
  //
  //  @Test def testKBagDifferent() {
  //    import org.kframework.koreimplementation
  //
  //    val foo = KBag(KLabel("foo"), koreimplementation.KList(1, 2, 3))
  //
  //    val pattern = KBag(KLabel("foo"), koreimplementation.KList(1, 3))
  //    assertEquals(False, pattern.matchAll(foo))
  //  }
  //
  //  @Test def testKBagWithVariable() {
  //    import org.kframework.koreimplementation
  //
  //    val foo = KBag(KLabel("foo"), koreimplementation.KList(1, 2, 3))
  //
  //    val pattern = KBag(KLabel("foo"), koreimplementation.KList(X))
  //    assertEquals(Or(And(X -> (1: K)), And(X -> (2: K)), And(X -> (3: K))), pattern.matchAll(foo))
  //  }
  //
  ////  @Test def testKBagWithTwoVariables() {
  ////    import org.kframework.koreimplementation
  ////
  ////    val foo = KBag(KLabel("foo"), koreimplementation.KList(1, 2, 3))
  ////
  ////    val pattern = KBag(KLabel("foo"), koreimplementation.KList(X))
  ////    assertEquals(Or(And(X -> (1: K)), And(X -> (2: K)), And(X -> (3: K))), pattern.matchAll(foo))
  ////  }
  //
  //  @Test def testKListAssoc1() {
  //    val foo = 'foo(5: K, 6)
  //
  //    val pattern = 'foo(X, Y)
  //    assertEquals(Or(And(X -> KList(), Y -> KList(5: K, 6)), And(X -> (5: K), Y -> (6: K)), And(X -> KList(5: K,
  // 6), Y -> KList())),
  //      pattern.matchAll(foo))
  //  }
  //
  //  @Test def testKListAssoc2() {
  //    val foo = 'foo(5: K, 7, 6)
  //
  //    val pattern = 'foo(X, 7, Y)
  //    assertEquals(Or(And(X -> (5: K), Y -> (6: K))),
  //      pattern.matchAll(foo))
  //  }
  //
  //  @Test def testKListAssoc3() {
  //    val foo = 'foo(5: K, 5: K, 5: K)
  //
  //    val pattern = 'foo(X, 5: K, Y)
  //    assertEquals(Or(And(X -> KList(), Y -> KList(5: K, 5: K)), And(X -> (5: K), Y -> (5: K)), And(X -> KList(5:
  // K, 5: K), Y -> KList())),
  //      pattern.matchAll(foo))
  //  }
  //
  //  @Test def testKListAssoc3WithCondition() {
  //    val foo = 'foo(5: K, 5: K, 5: K)
  //
  //    val pattern = 'foo(X, 5: K, Y)
  //    assertEquals(Or(And(X -> (5: K), Y -> (5: K))),
  //      pattern.matchAll(foo, Equals(X, 5: K)))
  //  }
  //
  //  @Test def testKListMultipleVar() {
  //    val foo = 'foo(5: K, 5: K)
  //    val pattern = 'foo(X, X)
  //    assertEquals(Or(And(X -> ((5: K): K))),
  //      pattern.matchAll(foo))
  //  }
  //
  //  @Test def testKListAssocMultipleVar() {
  //    val foo = 'foo(5: K, 5: K, 5: K)
  //    val pattern = 'foo(X, X)
  //    assertEquals(Or(), pattern.matchAll(foo))
  //  }
  //
  //  @Test def testKApplyWithEmptySeq() {
  //    val foo = 'foo()
  //    val pattern = 'foo(X)
  //    assertEquals(Some(And(X -> KList())), pattern.matchOne(foo))
  //  }
  //
  //  @Test def testKVariableMatchingKLabel() {
  //    val foo = 'foo()
  //    val pattern = KApply(X, Seq(), Att())
  //    assertEquals(Some(And(X -> MetaKLabel('foo))), pattern.matchOne(foo))
  //  }
  //
  //  // TODO: uningore when fixing side conditions
  //  @Test
  //  @Ignore def testKSeqAssoc() {
  //    val foo = KSequence(5: K, 5: K, 5: K)
  //
  //    val pattern = KSequence(X, 5: K, Y)
  //    assertEquals(Or(
  //      And(X -> KSequence(), Y -> KSequence(5: K, 5: K)),
  //      And(X -> KSequence(5: K), Y -> KSequence(5: K)),
  //      And(X -> KSequence(5: K, 5: K), Y -> KSequence())),
  //      pattern.matchAll(foo))
  //  }
  //
  //  @Test def testAttributes() {
  //    val foo = 'foo()
  //    assertEquals(Some(And(X -> foo)), X.matchOne(foo))
  //  }
  //
  //  @Test def testAnywhere() {
  //    val o = 'foo('bar('foo()))
  //    val a = Anywhere('foo(X))
  //    assertEquals(
  //      Or(And(X -> 'bar('foo()), a.TOPVariable -> a.HOLEVariable),
  //        And(X -> KList(), a.TOPVariable -> 'foo('bar(a.HOLEVariable)))),
  //      a.matchAll(o))
  //  }
  //
  //
  //  @Test def testTwoAnywheres() {
  //    val o = 'foo('foo('foo()))
  //    val inner = Anywhere('foo(X), "inner")
  //    val outer = Anywhere('foo(inner), "outer")
  //    println(outer)
  //    assertEquals(
  //      Or(And(X -> 'foo(), inner.TOPVariable -> inner.HOLEVariable, outer.TOPVariable -> outer.HOLEVariable),
  //        And(X -> KList(), inner.TOPVariable -> 'foo(inner.HOLEVariable), outer.TOPVariable -> outer.HOLEVariable),
  //        And(X -> KList(), inner.TOPVariable -> inner.HOLEVariable, outer.TOPVariable -> 'foo(outer.HOLEVariable))),
  //      outer.matchAll(o))
  //  }
  //
  //  def assertEquals(expected: Any, actual: Any) {
  //    if (expected != actual) {
  //      Assert.assertEquals(expected.toString(), actual.toString())
  //    }
  //  }

}
