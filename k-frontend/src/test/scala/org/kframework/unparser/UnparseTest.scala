// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.unparser

import org.junit.Assert
import org.junit.Test
import org.kframework.attributes.Att
import org.kframework.builtin.Sorts
import org.kframework.kore.ADT
import org.kframework.kore.KORE._

class UnparseTest {
  @Test def Token(): Unit =
    Assert.assertEquals("""#token("12","Int")""", ToKast(KToken("12", Sort("Int"))))

  @Test def EscapeLabel(): Unit =
    Assert.assertEquals("`_+_`", ToKast(KLabel("_+_")))

  @Test def WrappedKLabel(): Unit =
    Assert.assertEquals("#klabel(foo)", ToKast(InjectedKLabel(KLabel("foo"), Att.empty)))

  @Test def EmptyApp(): Unit =
    Assert.assertEquals("foo(.KList)", ToKast(KApply(KLabel("foo"))))

  @Test def NestedApp(): Unit =
    Assert.assertEquals(
      "foo(a(.KList),b(.KList))",
      ToKast(KApply(KLabel("foo"), KApply(KLabel("a")), KApply(KLabel("b"))))
    )

  @Test def SequenceEmpty(): Unit =
    Assert.assertEquals(".K", ToKast(ADT.KSequence(List(), Att.empty)))

  @Test def Sequence(): Unit =
    Assert.assertEquals(
      "a(.KList)~>b(.KList)~>c(.KList)",
      ToKast(Sugar.~>(KApply(KLabel("a")), Sugar.~>(KApply(KLabel("b")), KApply(KLabel("c")))))
    )

  @Test def Rewrite(): Unit =
    Assert.assertEquals(
      "a(.KList)=>b(.KList)",
      ToKast(KRewrite(KApply(KLabel("a")), KApply(KLabel("b"))))
    )

  @Test def Tokens(): Unit =
    Assert.assertEquals(
      """#token("9","Int")~>#token("Test","String")""",
      ToKast(Sugar.~>(KToken("9", Sorts.Int, Att.empty), KToken("Test", Sorts.String, Att.empty)))
    )

  @Test def Variables(): Unit =
    Assert.assertEquals("A=>B", ToKast(KRewrite(KVariable("A"), KVariable("B"))))

  @Test def Precedence1(): Unit =
    Assert.assertEquals(
      "``a(.KList)=>b(.KList)``~>c(.KList)",
      ToKast(Sugar.~>(KRewrite(KApply(KLabel("a")), KApply(KLabel("b"))), KApply(KLabel("c"))))
    )

  @Test def Precedence2(): Unit =
    Assert.assertEquals(
      "a(.KList)=>b(.KList)~>c(.KList)",
      ToKast(KRewrite(KApply(KLabel("a")), Sugar.~>(KApply(KLabel("b")), KApply(KLabel("c")))))
    )

  @Test def TickSpace(): Unit =
    Assert.assertEquals(
      "`` `_+_`(.KList)=>b(.KList)``~>c(.KList)",
      ToKast(Sugar.~>(KRewrite(KApply(KLabel("_+_")), KApply(KLabel("b"))), KApply(KLabel("c"))))
    )

  @Test def testKeywords(): Unit =
    Assert.assertEquals(
      "#a(.KList)~>`#klabel`(.KList)~>#klabel(test)~>`#token`(.KList)~>#token(\"1\",\"Int\")",
      ToKast(
        KSequence(
          KApply(KLabel("#a")),
          KApply(KLabel("#klabel")),
          InjectedKLabel(KLabel("test"), Att.empty),
          KApply(KLabel("#token")),
          KToken("1", Sort("Int"))
        )
      )
    )
}
