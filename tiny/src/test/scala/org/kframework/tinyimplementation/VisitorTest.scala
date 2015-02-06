// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.tinyimplementation

import org.junit.Test
import org.junit.Assert

class VisitorTest {
  import java.lang.Class
  import java.lang.reflect.Constructor

  trait Foo {
    def accept(x: DoubleDispatchVisitor)
  }
  case class Bar(x: Int, foo: Foo) extends Foo {
    def accept(x: DoubleDispatchVisitor) {
      x.visitBar(this)
      foo.accept(x)
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
    def visitBar(bar: Bar) { sumX += bar.x }
    def visitBuz(x: Buz.type) {}
  }

  case class FooReflectionVisitor() extends AbstractReflectiveVisitor {
    var sumX = 0
    def visit(foo: Bar) {
      sumX += foo.x
    }
  }

  @Test def testSimple {
    val visitor = FooReflectionVisitor()
    visitor(Bar(1, Bar(2, Buz)))
    Assert.assertEquals(3, visitor.sumX)
  }

  @Test def testPerformance {
    val manyBars = (1 to 100).foldLeft(Buz: Foo) { case (x, i) => Bar(i, x) }
    val expectedSum = 505000

    // by double dispatch
    var startTime = System.nanoTime()
    val ddvisitor = new FooDoubleDispatchVisitor()
    (1 to 100) foreach { i => manyBars.accept(ddvisitor) }
    Assert.assertEquals(expectedSum, ddvisitor.sumX)
    println((System.nanoTime() - startTime) / 1000)

    // by pattern matching
    startTime = System.nanoTime()
    class PM {
      var sumX = 0
      def apply(x: Foo): Unit = x match {
        case Bar(x, rest) =>
          sumX += x; apply(rest)
        case Buz =>
      }
    }
    val visitorPM = new PM()
    (1 to 100) foreach { i => visitorPM(manyBars) }
    Assert.assertEquals(expectedSum, visitorPM.sumX)
    println((System.nanoTime() - startTime) / 1000)

    // by reflection
    startTime = System.nanoTime()
    val visitor = FooReflectionVisitor()
    (1 to 100) foreach { i => visitor(manyBars) }
    Assert.assertEquals(expectedSum, visitor.sumX)
    println((System.nanoTime() - startTime) / 1000)

  }
}
