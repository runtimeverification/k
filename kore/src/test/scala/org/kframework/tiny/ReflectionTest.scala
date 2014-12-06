package org.kframework.tiny

import org.junit.Test

case class Foo(bar: Int = 6, buz: String)(zzz: String = "foo") {
  override def toString = s"Foo($bar,$buz)($zzz)"
}

class ReflectionTest {

  @Test def findObject() {
    assertEquals(Foo, Reflection.findObject("org.kframework.tiny.Foo"))
  }

  @Test def invokeMethod {
    val expected = Foo(2, "buzValue")("zzzValue")
    val actual = Reflection.invokeMethod(Foo, "apply", Seq(Seq(2, "buzValue"), Seq("zzzValue")))
    assertEquals(expected, actual)
  }

  def assertEquals(expected: Any, actual: Any) = {
    org.junit.Assert.assertEquals(expected, actual)
    org.junit.Assert.assertEquals(expected.toString(), actual.toString())
  }

  @Test def invokeMethodWithDefaultParamList {
    val expected = Foo(2, "buzValue")()
    val actual = Reflection.invokeMethod(Foo, "apply", Seq(Seq(2, "buzValue")))
    assertEquals(expected, actual)
  }

  @Test def invokeMethodWithDefaultArg {
    case class Bar(x: Int, y: String = "foo")
    val expected = Bar(3)
    val actual = Reflection.invokeMethod(Bar, "apply", Seq(Seq(3)))
    assertEquals(expected, actual)
  }
}
