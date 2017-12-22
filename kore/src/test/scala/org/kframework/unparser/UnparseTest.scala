package org.kframework.unparser

import org.junit.{Assert, Test}
import org.kframework.attributes.Att
import org.kframework.kore.ADT
import org.kframework.kore.KORE._

class UnparseTest {
  @Test def Token() {
    Assert.assertEquals("""#token("12","Int")""",ToKast(KToken("12", Sort("Int"))))
  }

  @Test def EscapeLabel() {
    Assert.assertEquals("`_+_`",ToKast(KLabel("_+_")))
  }

  @Test def WrappedKLabel() {
    Assert.assertEquals("#klabel(foo)",ToKast(InjectedKLabel('foo, Att.empty)))
  }

  @Test def EmptyApp() {
    Assert.assertEquals("foo(.KList)",ToKast('foo()))
  }

  @Test def NestedApp() {
    Assert.assertEquals("foo(a(.KList),b(.KList))",ToKast('foo('a(), 'b())))
  }

  @Test def SequenceEmpty() {
    Assert.assertEquals(".K",ToKast(ADT.KSequence(List(),Att.empty)))
  }

  @Test def Sequence() {
    Assert.assertEquals("a(.KList)~>b(.KList)~>c(.KList)",ToKast('a()~>'b()~>'c()))
  }

  @Test def Rewrite() {
    Assert.assertEquals("a(.KList)=>b(.KList)",ToKast(KRewrite('a(),'b())))
  }

  @Test def Tokens() {
    Assert.assertEquals("""#token("9","Int")~>#token("Test","String")""",ToKast(intToToken(9)~>"Test"))
  }

  @Test def Variables() {
    Assert.assertEquals("A=>B",ToKast(KRewrite(KVariable("A"),KVariable("B"))))
  }

  @Test def Precedence1() {
    Assert.assertEquals("``a(.KList)=>b(.KList)``~>c(.KList)",ToKast(KRewrite('a(),'b())~>'c()))
  }

  @Test def Precedence2() {
    Assert.assertEquals("a(.KList)=>b(.KList)~>c(.KList)",ToKast(KRewrite('a(),'b()~>'c())))
  }

  @Test def TickSpace() {
    Assert.assertEquals("`` `_+_`(.KList)=>b(.KList)``~>c(.KList)",ToKast(KRewrite(KLabel("_+_")(),'b())~>'c()))
  }

  @Test def testKeywords(): Unit = {
    Assert.assertEquals("#a(.KList)~>`#klabel`(.KList)~>#klabel(test)~>`#token`(.KList)~>#token(\"1\",\"Int\")",
      ToKast(KSequence(KLabel("#a")(),
        KLabel("#klabel")(), InjectedKLabel(KLabel("test"),Att.empty),
        KLabel("#token")(),  KToken("1", Sort("Int")))))
  }
}
