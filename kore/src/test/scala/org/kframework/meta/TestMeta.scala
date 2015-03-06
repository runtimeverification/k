//package org.kframework.tinyimplementation
//
//import java.io.File
//
//import org.kframework._
//import org.kframework.definition._
//import org.kframework.kore.KORE._
//import org.kframework.kore._
//
//class TestMeta {
//
//  import org.junit._
//
//
//  @Test def simple() {
//    assertEquals(1: K, Up(1))
//    assertEquals('List(1, 2, 3), Up(List[Int](1, 2, 3)))
//    assertEquals('Definition('Set('Require(KToken(Sort("File"), "foo.k"))), 'Set(), 'Att('Set())),
//      Up(Definition(Set(Require(new File("foo.k"))), Set())))
//
//    //    assertEquals('Foo(5), Meta(Foo(5)))
//  }
//
//  def assertEquals(x: Any, y: Any) { if (x != y) Assert.assertEquals(x.toString, y.toString) }
//
//  val d = Definition(Set(),
//    Set(Module("TEST", Set(),
//      Set(Production(Sort("Foo"),
//        List(Terminal("Bar")))))))
//
//  val metad = 'Definition('Set(),
//    'Set('Module("TEST", 'Set(),
//      'Set('Production('Sort("Foo"), 'List('Terminal("Bar")))))))
//
//  val Down = tinyimplementation.Down(Set("org.kframework.definition", "scala.collection.immutable"))
//
//  @Ignore
//  @Test def definitionUp() {
//    assertEquals(metad, Up(d))
//  }
//
//  @Test def assertUpDown() {
//    assertEquals(d, Down(Up(d)))
//  }
//
//  @Test def definitionDown() {
//    assertEquals(d, Down(metad))
//  }
//
//  @Test def testTransformation() {
//    val metaT = Up(d).searchFor(Anywhere(KRewrite('Sort("Foo"), 'Sort("Bar"))))
//  }
//}
