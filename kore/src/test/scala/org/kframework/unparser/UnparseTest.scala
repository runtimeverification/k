// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.unparser

import org.junit.Assert
import org.junit.Test
import org.kframework.attributes.Att
import org.kframework.builtin.Sorts
import org.kframework.kore.ADT
import org.kframework.kore.KORE._

class UnparseTest {
  @Test def Token() {
    Assert.assertEquals("""#token("12","Int")""", ToKast(KToken("12", Sort("Int"))))
  }

  @Test def EscapeLabel() {
    Assert.assertEquals("`_+_`", ToKast(KLabel("_+_")))
  }

  @Test def WrappedKLabel() {
    Assert.assertEquals("#klabel(foo)", ToKast(InjectedKLabel(KLabel("foo"), Att.empty)))
  }

  @Test def EmptyApp() {
    Assert.assertEquals("foo(.KList)", ToKast(KApply(KLabel("foo"))))
  }

  @Test def NestedApp() {
    Assert.assertEquals(
      "foo(a(.KList),b(.KList))",
      ToKast(KApply(KLabel("foo"), KApply(KLabel("a")), KApply(KLabel("b"))))
    )
  }

  @Test def SequenceEmpty() {
    Assert.assertEquals(".K", ToKast(ADT.KSequence(List(), Att.empty)))
  }

  @Test def Sequence() {
    Assert.assertEquals(
      "a(.KList)~>b(.KList)~>c(.KList)",
      ToKast(Sugar.~>(KApply(KLabel("a")), Sugar.~>(KApply(KLabel("b")), KApply(KLabel("c")))))
    )
  }

  @Test def Rewrite() {
    Assert.assertEquals(
      "a(.KList)=>b(.KList)",
      ToKast(KRewrite(KApply(KLabel("a")), KApply(KLabel("b"))))
    )
  }

  @Test def Tokens() {
    Assert.assertEquals(
      """#token("9","Int")~>#token("Test","String")""",
      ToKast(Sugar.~>(KToken("9", Sorts.Int, Att.empty), KToken("Test", Sorts.String, Att.empty)))
    )
  }

  @Test def Variables() {
    Assert.assertEquals("A=>B", ToKast(KRewrite(KVariable("A"), KVariable("B"))))
  }

  @Test def Precedence1() {
    Assert.assertEquals(
      "``a(.KList)=>b(.KList)``~>c(.KList)",
      ToKast(Sugar.~>(KRewrite(KApply(KLabel("a")), KApply(KLabel("b"))), KApply(KLabel("c"))))
    )
  }

  @Test def Precedence2() {
    Assert.assertEquals(
      "a(.KList)=>b(.KList)~>c(.KList)",
      ToKast(KRewrite(KApply(KLabel("a")), Sugar.~>(KApply(KLabel("b")), KApply(KLabel("c")))))
    )
  }

  @Test def TickSpace() {
    Assert.assertEquals(
      "`` `_+_`(.KList)=>b(.KList)``~>c(.KList)",
      ToKast(Sugar.~>(KRewrite(KApply(KLabel("_+_")), KApply(KLabel("b"))), KApply(KLabel("c"))))
    )
  }

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
