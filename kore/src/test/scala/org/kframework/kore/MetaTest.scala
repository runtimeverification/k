package org.kframework.kore

import KORE._
import KInt._

case class Foo(a: Int)

class MetaTest {
  import org.junit._
  import Assert._

  @Test
  def simple() {
    assertEquals('Foo(1), Meta(Foo(1)))
    assertEquals(KList(1, 2, 3), Meta(List[Int](1, 2, 3)))
  }
}