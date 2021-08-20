// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework.definition

import org.junit.{Assert, Test}

trait Foo {
  def accept(x: DoubleDispatchVisitor): Unit
}
case class Bar(x: Int, foo: Foo) extends Foo {
  def accept(x: DoubleDispatchVisitor): Unit = {
    x.visitBar(this)
    foo.accept(x)
  }
}
object Buz extends Foo {
  def accept(x: DoubleDispatchVisitor): Unit = {
    x.visitBuz(this)
  }
}

trait DoubleDispatchVisitor {
  def visitBar(x: Bar): Unit
  def visitBuz(x: Buz.type): Unit
}

class FooDoubleDispatchVisitor extends DoubleDispatchVisitor {
  var sumX = 0
  def visitBar(bar: Bar): Unit = { sumX += bar.x }
  def visitBuz(x: Buz.type): Unit = {}
}



class VisitorTest {

}
