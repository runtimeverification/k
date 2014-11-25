package org.kframework.kore

import KORE._
import KInt._
import org.kframework.kore.outer._
import java.io.File

case class Foo(a: Int)

class MetaTest {
  import org.junit._
  import Assert._

  @Test
  def simple() {
    assertEquals('Foo(1), Meta(Foo(1)))
    assertEquals(KList(1, 2, 3), Meta(List[Int](1, 2, 3)))
    assertEquals('Definition(KSet('Require(KToken(Sort("File"), "foo.k"))), KSet()),
      Meta(Definition(Set(Require(new File("foo.k"))), Set())))

    //    val c = Concrete(Set())
    //    println(c(Meta(Foo(2))))
  }
}
