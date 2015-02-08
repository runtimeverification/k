package org.kframework.meta

import org.junit.Test

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
    assertEquals(Foo, Reflection.findObject("org.kframework.meta.Foo"))
  }

  @Test def findSet() {
    assertEquals(scala.collection.Set, Reflection.findObject("scala.collection.Set"))
  }

  @Test def invokeMethod {
    val expected = Foo(2, "buzValue")("zzzValue")
    val actual = Reflection.invokeMethod(Foo, "apply", Seq(Seq(2, "buzValue"), Seq("zzzValue")))
    assertEquals(expected, actual)
  }

  @Test def invokeMethodVararg {
    val actual = Reflection.invokeMethod(Set, "apply", Seq(Seq(2, "buzValue")))
    assertEquals(Set(2, "buzValue"), actual)
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
      Reflection.construct("org.kframework.meta.Bar", Seq(4, "Foo")))
  }

  @Test def performanceTest {
    val b = Bar(2)

    val interval = (1 to Int.MaxValue / 10000)
    // warmup
    interval foreach { x => 1 }
    interval foreach { x => 1 }
    interval foreach { x => 1 }

    var startTime = System.nanoTime()
    interval foreach { x => 1 }
    val diffTime = System.nanoTime() - startTime

    // direct call
    startTime = System.nanoTime()
    interval foreach { x => b.buz(3) }
    //    println((System.nanoTime() - startTime - diffTime) / 1000)

    // Scala reflection
    val method = Reflection.mirrorForMethod(b,
      Reflection.findMethod(b, "buz", Seq(Seq(3.getClass.asInstanceOf[Class[Any]])))._1)
    startTime = System.nanoTime()
    interval foreach { x => method(3) }
    //    println((System.nanoTime() - startTime - diffTime) / 1000)

    // Java reflection
    val javaMethod = b.getClass.getMethod("buz", 3.getClass())
    startTime = System.nanoTime()
    interval foreach { x => javaMethod.invoke(b, 3.asInstanceOf[Object]) }
    //    println((System.nanoTime() - startTime - diffTime) / 1000)
  }
}
