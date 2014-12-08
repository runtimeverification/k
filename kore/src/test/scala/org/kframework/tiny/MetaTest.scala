package org.kframework.tiny

import org.kframework._
import kore._
import KORE._
import java.io.File
import kore.outer._
import scala.reflect.ClassTag

class MetaTest {
  import org.junit._

  import KToken._

  @Test def simple() {
    assertEquals(1: K, Up(1))
    assertEquals('List(1, 2, 3), Up(List[Int](1, 2, 3)))
    assertEquals('Definition('Set('Require(KToken(Sort("File"), "foo.k"))), 'Set(), 'Attributes('Set())),
      Up(Definition(Set(Require(new File("foo.k"))), Set())))

    //    assertEquals('Foo(5), Meta(Foo(5)))
  }

  def assertEquals(x: Any, y: Any) { if (x != y) Assert.assertEquals(x.toString, y.toString) }

  import outer._

  val d = Definition(Set(),
    Set(Module("TEST",
      Set(SyntaxProduction(Sort("Foo"),
        List(Terminal("Bar")))))))

  val metad = 'Definition('Set(),
    'Set('Module("TEST",
      'Set('SyntaxProduction('Sort("Foo"), 'List('Terminal("Bar")))))))

  val Down = tiny.Down(Set("org.kframework.kore.outer"))

  @Test def definitionUp() {
    assertEquals(metad, Up(d))
  }

  @Test def assertUpDown() {
    assertEquals(d, Down(Up(d)))
  }

  @Test def definitionDown() {
    assertEquals(d, Down(metad))
  }

  @Test def testTransformation() {
    val metaT = Up(d).search(Anywhere(KRewrite('Sort("Foo"), 'Sort("Bar"))))
  }
}
