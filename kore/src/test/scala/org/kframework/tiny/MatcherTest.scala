package org.kframework.tiny

import org.junit.{Assert, Ignore, Test}

class MatcherTest extends AbstractTest {

  import cons._

  implicit class KWithMatcherMethods(k: K) {
    def matchAll(other: K, sideConditions: K = True): K = And(k.matcher(other), sideConditions).normalize match {
      case or: Or => or
      case k => k
    }
    def matchOne(other: K, sideConditions: K = True) = matchAll(other, sideConditions) match {
      case or: Or if or.children.size > 0 => or.children.head
      case x => x
    }
  }

  @Test def testSimple() {
    assertEquals(X -> 'foo(), X.matcher('foo()).normalize)
  }

  @Test def testSimpleWithFalseSideCondition() {
    val foo = 'foo()

    println(And(X.matcher('foo())))

    assertEquals(False, And(X.matcher('foo()), False).normalize)
  }

  @Test def testSimpleWithTrueSideCondition() {
    val foo = 'foo()
    Assert.assertEquals(And(X -> 'foo()), X.matchAll(foo, True))
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

  @Test def testKApplyWithCondition() {
    val foo = 'foo(5: K)
    val pattern = 'foo(X)
    assertEquals(And(X -> ((5: K): K)), pattern.matchOne(foo, Equals(X, 5: K)))
  }

  @Test def testKApplyWithFailingCondition() {
    val foo = 'foo(5: K)
    val pattern = 'foo(X)
    assertEquals(False, pattern.matchAll(foo, Equals(X, 4: K)))
  }

  @Test
  @Ignore def testKApplyIdWithFailingCondition() {
    val foo = 'foo(5: K, 6: K)
    val pattern = 'foo(X, Y)
    assertEquals(False, pattern.matchAll(foo, Equals(X, Y)))
  }

  @Test
  @Ignore def testKApplyIdWithPassingCondition() {
    val foo = 'foo(5: K, 5: K)
    val pattern = 'foo(X, Y)
    assertEquals(Or(And(X -> (5: K), Y -> (5: K))), pattern.matchAll(foo, Equals(X, Y)))
  }

  @Test def testKApply1() {
    val foo = 'foo(5)
    val pattern = 'bar(X)
    assertEquals(False, pattern.matchOne(foo))
  }

  @Test def testNested() {
    assertEquals(And(X -> ((5: K): K)), 'foo('bar(X)).matchAll('foo('bar(5: K))))
  }

  @Test def testAssocEntire() {
    val foo = (5: K) + 6
    val pattern = X
    assertEquals(And(X -> foo), pattern.matchAll(foo))
  }

  @Test def testAssocPrefix() {
    val foo = (5: K) + 6 + 7
    val pattern = X + 7
    assertEquals(Or(And(X -> ((5: K) + 6))), pattern.matchAll(foo))
  }

  @Test def testAssocPostfix() {
    val foo = (5: K) + 6 + 7
    val pattern = (5: K) + X
    assertEquals(Or(And(X -> ((6: K) + 7))), pattern.matchAll(foo))
  }

  @Test def testAssocMiddle() {
    val foo = (5: K) + 6 + 7 + 8
    val pattern = (5: K) + X + 8
    assertEquals(Or(And(X -> ((6: K) + 7))), pattern.matchAll(foo))
  }

  @Test def testAssocMultivar() {
    val foo = (5: K)
    val pattern = X + Y
    assertEquals(Or(And(X -> '+(), Y -> 5), And(X -> 5, Y -> '+())), pattern.matchAll(foo))
  }

  @Test def testAssocMultivar1() {
    val foo = (5: K) + 6
    val pattern = X + Y
    assertEquals(Or(
      And(Y -> '+(5, 6), X -> '+()),
      And(Y -> 6, X -> 5),
      And(Y -> '+(), X -> '+(5, 6))),
      pattern.matchAll(foo))
  }

  @Test def testAssocMultivar2() {
    val foo = (5: K) + 6 + 7
    val pattern = X + 6 + Y
    assertEquals(Or(And(Y -> 7, X -> 5)), pattern.matchAll(foo))
  }

  @Test def testAssocMultivar3() {
    val foo = (5: K) + 5 + 5
    val pattern = X + 5 + Y
    assertEquals(Or(
      And(X -> '+(), Y -> ((5: K) + 5)),
      And(X -> 5, Y -> 5),
      And(X -> ((5: K) + 5), Y -> '+())
    ), pattern.matchAll(foo))
  }

  @Test def testAssocMultivar3WithCond() {
    val foo = (5: K) + 5 + 5
    val pattern = X + 5 + Y
    assertEquals(Or(
      And(X -> 5, Y -> 5)
    ), pattern.matchAll(foo, Equals(X, 5: K)))
  }

  @Test def testKListMultipleVar() {
    val foo = '+(5: K, 5: K)
    val pattern = '+(X, X)
    assertEquals(Or(And(X -> (5: K))),
      pattern.matchAll(foo))
  }

  @Test def testKListAssocMultipleVar() {
    val foo = '+(5: K, 5: K, 5: K)
    val pattern = '+(X, X)
    assertEquals(False, pattern.matchAll(foo))
  }

  @Test def testKApplyWithEmptySeq() {
    val foo = '+()
    val pattern = '+(X)
    assertEquals(And(X -> '+()), pattern.matchOne(foo))
  }

//  @Test def testKVariableMatchingKLabel() {
//    val foo = 'foo()
//    val pattern = KApp(X, Seq(), Att())
//    assertEquals(And(X -> InjectedKLabel('foo)), pattern.matchOne(foo))
//  }

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
