package org.kframework.kore

import KInt._

class KoreTest {
  import org.junit._

  object TestK extends KApply(KLabel("Test"), KList())

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
    val x = KSequence(TestK, TestK) copy Attributes(TestK)
    val t: KSequence = x map { t: K => t }
    assertEquals(Attributes(TestK), t.att)
    assertEquals(x, t)
  }

  @Test def testKApply {
    val x = KApply(KLabel("foo"), Seq(TestK)) copy Attributes(TestK)
    val t: KApply = x map { t: K => t }
    assertEquals(Attributes(TestK), t.att)
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
    assertEquals(KList(TestK), KList(KList(TestK)))
  }

  @Test def testKRewrite {
    val x = KRewrite(TestK, TestK) copy Attributes(TestK)
    val y = KRewrite(TestK, TestK) copy Attributes(TestK)
    assertEquals(x, y)
  }

  @Test def testKApplyEquals {
    assertNotEquals(KApply(KLabel("foo"), KList(), Attributes()), KApply(KLabel("bar"), KList(), Attributes()))
    assertNotEquals(KApply(KLabel("foo"), KList(), Attributes()), KList())
    assertNotEquals(KList(), KApply(KLabel("foo"), KList(), Attributes()))
    assertNotEquals(KList(5), KApply(KLabel("foo"), KList(5), Attributes()))
    assertNotEquals(KApply(KLabel("foo"), KList(5), Attributes()), KList(5))
  }

}
