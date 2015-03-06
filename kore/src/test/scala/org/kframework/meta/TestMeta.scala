package org.kframework.tinyimplementation

import java.io.File

import org.kframework.definition._
import org.kframework.kore._
import org.kframework.meta.{Down, Up}

class TestMeta {

  import org.junit._

  val up = new Up(KORE)
  val down = Down(Set(
    "org.kframework.definition",
    "scala.collection.immutable",
    "org.kframework.kore.ADT"))

  import org.kframework.kore.KORE._

  @Test def simple() {
    assertEquals(1: K, up(1))
    assertEquals('List(1, 2, 3), up(List[Int](1, 2, 3)))
    assertEquals('Definition('Set('Require(KToken(Sort("File"), "foo.k"))), 'Set(),
      KLabel("org.kframework.attributes.Att")('Set())),
      up(Definition(Set(Require(new File("foo.k"))), Set())))

    //    assertEquals('Foo(5), Meta(Foo(5)))
  }

  def assertEquals(x: Any, y: Any) { if (x != y) Assert.assertEquals(x.toString, y.toString) }

  val d = Definition(Set(),
    Set(Module("TEST", Set(),
      Set(Production("Foo", Sort("Foo"), Seq(Terminal("Bar")))))))

  val metad = 'Definition('Set(),
    'Set('Module("TEST", 'Set(),
      'Set('Production("Foo", 'Sort("Foo"), 'List('Terminal("Bar")))))))


  @Ignore
  @Test def definitionup() {
    assertEquals(metad, up(d))
  }

//  @Test def assertUpDown() {
//    assertEquals(d, down(up(d)))
//  }

  @Test def definitionDown() {
    assertEquals(d, down(metad))
  }

  //  @Test def testTransformation() {
  //    val metaT = up(d).searchFor(Anywhere(KRewrite('Sort("Foo"), 'Sort("Bar"))))
  //  }
}
