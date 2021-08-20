package org.kframework.unparser

import org.junit.{Assert, Test}
import org.kframework.attributes.Att
import org.kframework.kore.ADT
import org.kframework.kore.KORE._

class UnparseTest {
  @Test def Token(): Unit = {
    Assert.assertEquals("""#token("12","Int")""",ToKast(KToken("12", Sort("Int"))))
  }

  @Test def EscapeLabel(): Unit = {
    Assert.assertEquals("`_+_`",ToKast(KLabel("_+_")))
  }

  @Test def WrappedKLabel(): Unit = {
    Assert.assertEquals("#klabel(foo)",ToKast(InjectedKLabel(Symbol("foo"), Att.empty)))
  }

  @Test def EmptyApp(): Unit = {
    Assert.assertEquals("foo(.KList)",ToKast(Symbol("foo")()))
  }

  @Test def NestedApp(): Unit = {
    Assert.assertEquals("foo(a(.KList),b(.KList))",ToKast(Symbol("foo")(Symbol("a")(), Symbol("b")())))
  }

  @Test def SequenceEmpty(): Unit = {
    Assert.assertEquals(".K",ToKast(ADT.KSequence(List(),Att.empty)))
  }

  @Test def Sequence(): Unit = {
    Assert.assertEquals("a(.KList)~>b(.KList)~>c(.KList)",ToKast(Symbol("a")()~>Symbol("b")()~>Symbol("c")()))
  }

  @Test def Rewrite(): Unit = {
    Assert.assertEquals("a(.KList)=>b(.KList)",ToKast(KRewrite(Symbol("a")(),Symbol("b")())))
  }

  @Test def Tokens(): Unit = {
    Assert.assertEquals("""#token("9","Int")~>#token("Test","String")""",ToKast(intToToken(9)~>"Test"))
  }

  @Test def Variables(): Unit = {
    Assert.assertEquals("A=>B",ToKast(KRewrite(KVariable("A"),KVariable("B"))))
  }

  @Test def Precedence1(): Unit = {
    Assert.assertEquals("``a(.KList)=>b(.KList)``~>c(.KList)",ToKast(KRewrite(Symbol("a")(),Symbol("b")())~>Symbol("c")()))
  }

  @Test def Precedence2(): Unit = {
    Assert.assertEquals("a(.KList)=>b(.KList)~>c(.KList)",ToKast(KRewrite(Symbol("a")(),Symbol("b")()~>Symbol("c")())))
  }

  @Test def TickSpace(): Unit = {
    Assert.assertEquals("`` `_+_`(.KList)=>b(.KList)``~>c(.KList)",ToKast(KRewrite(KLabel("_+_")(),Symbol("b")())~>Symbol("c")()))
  }

  @Test def testKeywords(): Unit = {
    Assert.assertEquals("#a(.KList)~>`#klabel`(.KList)~>#klabel(test)~>`#token`(.KList)~>#token(\"1\",\"Int\")",
      ToKast(KSequence(KLabel("#a")(),
        KLabel("#klabel")(), InjectedKLabel(KLabel("test"),Att.empty),
        KLabel("#token")(),  KToken("1", Sort("Int")))))
  }
}
