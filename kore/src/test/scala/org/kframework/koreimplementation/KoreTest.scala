package org.kframework.koreimplementation

import org.kframework.builtin.Sorts
import org.kframework.attributes._

class KoreTest {
  import org.junit._

  object TestK extends KSimpleApply(KLabel("Test"), KList())

  import Assert._

  @Test def testKListMapId {
    val x = KList(TestK, TestK)
    val t: KList = x map { t: K => t }
    assertEquals(KList(TestK, TestK), t)
  }

  @Test def testKSequenceMapId {
    val x = KSequence(TestK, TestK)
    val t: KSequence = x map { t: K => t }
    assertEquals(KSequence(TestK, TestK), t)
  }

  @Test def reduceKSequence {
    val x = KSequence(TestK, TestK)
  }

  @Test def testKSequenceMapRetainsAttributes {
    val x = KSequence(TestK, TestK) copy Att(TestK)
    val t: KSequence = x map { t: K => t }
    assertEquals(Att(TestK), t.att)
    assertEquals(x, t)
  }

  @Test def testKApply {
    val x = KApply(KLabel("foo"), Seq(TestK)) copy Att(TestK)
    val t: KApply = x map { t: K => t }
    assertEquals(Att(TestK), t.att)
    assertEquals(x, t)
  }

  @Test def testKList {
    val x = KList(TestK, TestK)
    x match {
      case KList(a, b) =>
      case _ => throw new RuntimeException("match fail")
    }
  }

  @Test def testKListAssoc {
    //    assertEquals(KList(TestK), KList(KList(TestK)))
  }

  @Test def testKRewrite {
    val x = KRewrite(TestK, TestK) copy Att(TestK)
    val y = KRewrite(TestK, TestK) copy Att(TestK)
    assertEquals(x, y)
  }

  @Test def testKApplyEquals {
    assertNotEquals(KApply(KLabel("foo"), KList(), Att()), KApply(KLabel("bar"), KList(), Att()))
    assertNotEquals(KApply(KLabel("foo"), KList(), Att()), KList())
    assertNotEquals(KList(), KApply(KLabel("foo"), KList(), Att()))
    assertNotEquals(KList(KToken(Sorts.Int, "5")), KApply(KLabel("foo"), KList(KToken(Sorts.Int, "5")), Att()))
    assertNotEquals(KApply(KLabel("foo"), KList(KToken(Sorts.Int, "5")), Att()), KList(KToken(Sorts.Int, "5")))
  }

  @Test def testKSequenceEquals {
    assertEquals(KSequence(TestK), KSequence(TestK))
    assertEquals(KSequence(TestK, TestK), KSequence(TestK, TestK))
  }

  @Test def testAttributes {
    assertEquals("[]", Att().toString())
    assertEquals("", Att().postfixString)
    assertEquals(" [X]", Att(KVariable("X")).postfixString)
  }

}
