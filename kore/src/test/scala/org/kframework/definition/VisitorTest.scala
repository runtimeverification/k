// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework.definition

import org.junit.{Assert, Test}

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



class VisitorTest {

}
