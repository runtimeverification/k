package org.kframework.kore

class KoreTest {
  import org.junit._

  case object TestK extends K {
    def att: org.kframework.kore.Attributes = ???
    def copy(att: org.kframework.kore.Attributes): TestK.ThisK = ???
  }

  import Assert._

  @Test def testKListMapId {
    val x = KList(TestK, TestK)
    val t: KList = x map { t => t }
    assertEquals(KList(TestK, TestK), t)
  }

  @Test def testAttributesMapId {
    val x = Attributes(KList(TestK, TestK))
    val t: Attributes = x map { t => t }
    assertEquals(Attributes(KList(TestK, TestK)), t)
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
    val x = KApply(KLabel("foo"), TestK) copy Attributes(TestK)
    val t: KApply = x map { t: K => t }
    assertEquals(Attributes(TestK), t.att)
    assertEquals(x, t)
  }

  @Test(expected = classOf[UnsupportedOperationException])
  def testCannotCreateKApplyFromJustKs {
    KApply(TestK)
  }

  @Test def testKRewrite {
    val x = KRewrite(TestK, TestK) copy Attributes(TestK)
    //    val t: KRewrite = x map { t => t }
    //    assertEquals(x, t)
  }
}
