package org.kframework.tiny

import org.junit.Test
import org.junit.rules.ExpectedException

case class Foo(bar: Int = 6, buz: String)(zzz: String = "foo") {
  override def toString = s"Foo($bar,$buz)($zzz)"
}

case class Bar(x: Int, y: String = "foo") {
  def buz(x: Any) = "any"
  def buz(x: Int) = "int"
  def buz(s: String) = "string"
  def buz(n: Number) = "number"
  def buz(s: Int, v: Int) = "intint"
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
    val expected = Bar(3)
    val actual = Reflection.invokeMethod(Bar, "apply", Seq(Seq(3)))
    assertEquals(expected, actual)
  }

  @Test def invokeOverloadedMethod {
    val o = Bar(3)
    assertEquals("int", Reflection.invokeMethod(o, "buz", Seq(Seq(3))))
    assertEquals("intint", Reflection.invokeMethod(o, "buz", Seq(Seq(3, 4))))
    assertEquals("string", Reflection.invokeMethod(o, "buz", Seq(Seq("blabla"))))
    assertEquals("number", Reflection.invokeMethod(o, "buz", Seq(Seq(3.4))))
    assertEquals("any", Reflection.invokeMethod(o, "buz", Seq(Seq(o))))
  }

  @Test(expected = classOf[NoSuchMethodException])
  def missingMethod {
    Reflection.invokeMethod(Bar(3), "missing", Seq(Seq()))
  }

  @Test(expected = classOf[IllegalArgumentException])
  def illigalArgument {
    Reflection.invokeMethod(Bar(3), "buz", Seq(Seq()))
  }

  @Test def constructObject {
    assertEquals(Bar(4, "Foo"),
      Reflection.construct("org.kframework.tiny.Bar", Seq(4, "Foo")))
  }
}
