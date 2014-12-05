package org.kframework.kore

import KORE._
import KInt._
import KString._
import org.kframework.kore.outer._
import java.io.File
import org.kframework.kore.outer._
import org.kframework.tiny.Anywhere

case class Foo(i: Int)

class MetaTest {
  import org.junit._
  import Assert._

  @Test
  def simple() {
    assertEquals(1: K, Meta(KInt(1)))
    assertEquals('List(1, 2, 3), Meta(List[Int](1, 2, 3)))
    assertEquals('Definition('Set('Require(KToken(Sort("File"), "foo.k"))), 'Set()),
      Meta(Definition(Set(Require(new File("foo.k"))), Set())))

    assertEquals('Foo(5), Meta(Foo(5)))

    println(Concrete(Meta(KInt(2))))
  }

  import outer._

  val d = Definition(Set(),
    Set(Module("TEST",
      Set(SyntaxProduction(Sort("Foo"),
        Seq(Terminal("Bar")))))))

  val metad = 'Definition('Set(),
    'Set('Module("TEST",
      'Set('SyntaxProduction('Sort("Foo"), 'List('Terminal("Bar")), 'Attributes('Set()))),
      'Attributes('Set()))))

  @Test def definitionMeta() {
    assertEquals(metad, Meta(d))
  }

  @Test def definitionConcrete() {
    assertEquals(d, Concrete(metad))
  }

  @Test def testTransformation() {
    val metaT = Meta(d).search(Anywhere(KRewrite('Sort("Foo"), 'Sort("Bar"))))
    println(metaT)
    //    println(Concrete(metaT))
  }
}
