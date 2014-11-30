package org.kframework.kore

import KORE._
import KInt._
import org.kframework.kore.outer._
import java.io.File

case class Foo(i: Int)

class MetaTest {
  import org.junit._
  import Assert._

  @Test
  def simple() {
    assertEquals(1: K, Meta(KInt(1)))
    assertEquals(KList(1, 2, 3), Meta(List[Int](1, 2, 3)))
    assertEquals('Definition(KSet('Require(KToken(Sort("File"), "foo.k"))), KSet()),
      Meta(Definition(Set(Require(new File("foo.k"))), Set())))

   assertEquals('Foo(5), Meta(Foo(5)))

    val c = Concrete(Set())
    println(c(Meta(KInt(2))))
  }
  
//  @Test def definition() {
//    import outer._
//
//    val d = Definition(Set(), Set(Module("TEST", Set(SyntaxProduction(Sort("Foo"), Seq(Terminal("Bar")))))))
//
//    val expectedMetaD = 'Definition(KSet(),KSet('Module("TEST",
//        KSet('SyntaxProduction('UninterpretedSort("Foo"),'Terminal("Bar"),'Attributes(KSet()))),'Attributes(KSet()))))
//
//    println(Meta(d))
//  }
}
