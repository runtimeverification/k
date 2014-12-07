// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.outer

import org.junit.Test
import org.kframework.tiny.Reflection
import org.junit.Assert

abstract class AbstractVisitor {
  def apply(o: Any) {
    Reflection.invokeMethod(this, "visit", Seq(Seq(o)))
    Reflection.deconstruct(o) foreach apply
  }
  def visit(x: AnyRef) {}
}

trait Foo {
  def accept(x: DoubleDispatchVisitor)
}
case class Bar(x: Int, foo: Foo) extends Foo {
  def accept(x: DoubleDispatchVisitor) {
    x.visitBar(this)
  }
}
object Buz extends Foo {
  def accept(x: DoubleDispatchVisitor) {
    x.visitBuz(this)
  }
}

trait DoubleDispatchVisitor {
  def visitBar(x: Bar)
  def visitBuz(x: Buz.type)
}

class FooDoubleDispatchVisitor extends DoubleDispatchVisitor {
  var sumX = 0
  def visitBar(x: Bar) { sumX += x.x }
  def visitBuz(x: Buz.type) {}
}

class VisitorTest {
  import java.lang.Class
  import java.lang.reflect.Constructor

  case class FooVisitor() extends AbstractVisitor {
    var sumX = 0
    def visit(foo: Bar) {
      sumX += foo.x
    }
  }

  @Test def testSimple {
    val visitor = FooVisitor()
    visitor(Bar(1, Bar(2, Buz)))
    Assert.assertEquals(3, visitor.sumX)
  }

  @Test def testPerformance {
    val manyBars = (0 to 2000).foldLeft(Buz: Foo) { case (x, i) => Bar(i, x) }

    // by double dispatch
    var startTime = System.nanoTime()
    val ddvisitor = new FooDoubleDispatchVisitor()
    (0 to 10) foreach { i => manyBars.accept(ddvisitor) }
    println((System.nanoTime() - startTime) / 1000)

    // by pattern matching
    startTime = System.nanoTime()
    class PM {
      var x = 0
      def apply(x: Foo): Unit = x match {
        case Bar(x, rest) => apply(rest)
        case Buz =>
      }
    }
    (0 to 10) foreach { i => new PM()(manyBars) }
    println((System.nanoTime() - startTime) / 1000)

    // by reflection
    startTime = System.nanoTime()
    val visitor = FooVisitor()
    (0 to 10) foreach { i => visitor(manyBars) }
    Assert.assertEquals(22011000, visitor.sumX)
    println((System.nanoTime() - startTime) / 1000)

  }
}
