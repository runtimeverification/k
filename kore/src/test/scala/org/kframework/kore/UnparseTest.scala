package org.kframework.kore

import org.junit.{Assert, Test}
import org.kframework.attributes.Att
import org.kframework.kore.KORE._

class UnparseTest {
  @Test def Token() {
    Assert.assertEquals("""#token("Int","12")""",ToKast(KToken(Sort("Int"), "12")))
  }

  @Test def SimpleLabel() {
    Assert.assertEquals("foo",ToKast('foo))
  }
  @Test def EscapeLabel() {
    Assert.assertEquals("`_+_`",ToKast(KLabel("_+_")))
  }

  @Test def WrappedKLabel() {
    Assert.assertEquals("#klabel(foo)",ToKast(InjectedKLabel('foo, Att())))
  }

  @Test def EmptyApp() {
    Assert.assertEquals("foo()",ToKast('foo()))
  }

  @Test def NestedApp() {
    Assert.assertEquals("foo(a(),b())",ToKast('foo('a(), 'b())))
  }

  @Test def SequenceEmpty() {
    Assert.assertEquals(".K",ToKast(ADT.KSequence(List(),Att())))
  }

  @Test def Sequence() {
    Assert.assertEquals("a()~>b()~>c()",ToKast('a()~>'b()~>'c()))
  }

  @Test def Rewrite() {
    Assert.assertEquals("a()=>b()",ToKast(KRewrite('a(),'b())))
  }

  @Test def Tokens() {
    Assert.assertEquals("""#token("Int","9")~>#token("String","Test")""",ToKast(intToToken(9)~>"Test"))
  }

  @Test def Variables() {
    Assert.assertEquals("A=>B",ToKast(KRewrite(KVariable("A"),KVariable("B"))))
  }

  @Test def Precedence1() {
    Assert.assertEquals("``a()=>b()``~>c()",ToKast(KRewrite('a(),'b())~>'c()))
  }

  @Test def Precedence2() {
    Assert.assertEquals("a()=>b()~>c()",ToKast(KRewrite('a(),'b()~>'c())))
  }

  @Test def TickSpace() {
    Assert.assertEquals("`` `_+_`()=>b()``~>c()",ToKast(KRewrite(KLabel("_+_")(),'b())~>'c()))
  }
}
