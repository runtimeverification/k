//package org.kframework.definition
//
//import org.junit.Test
//import org.junit.Assert._
//import org.kframework.kore._
//import org.kframework.kore.ADTConstructors._
//
//import collection.immutable._
//import org.junit.Assert
//
//abstract class Visitor {
//  def visit(o: Product) = {
//
//  }
//}
//
//class OuterTest {
//
//  val testSyntaxModule = Module("TEST-SYNTAX", Set(), Set(SyntaxSort(Sort("Int"))))
//
//  @Test def testCorrect {
//
//    val dCorrect = Module("TEST", Set(testSyntaxModule), Set(
//      Production(KLabel("Exp"), Sort("Exp"), Seq(NonTerminal(Sort("Int"))))))
//  }
//
//  @Test def testIncorrect {
//    try {
//      Module("TEST", Set(testSyntaxModule), Set(
//        Production(Sort("Int"), Seq(NonTerminal(Sort("Exp"))))))
//
//      Assert.fail("Should have failed.")
//    } catch {
//      case NonTerminalsWithUndefinedSortException(set) if set == Set(NonTerminal(Sort("Exp"))) =>
//    }
//  }
//
//  @Test def testIncorrect1 {
//    try {
//      val testSyntaxModule = Module("TEST-SYNTAX", Set(), Set(
//        Production(Sort("Exp"), Seq(NonTerminal(Sort("Int"))))))
//
//      Module("TEST", Set(testSyntaxModule), Set(SyntaxSort(Sort("Int"))))
//
//      Assert.fail("Should have failed.")
//    } catch {
//      case NonTerminalsWithUndefinedSortException(set) if set == Set(NonTerminal(Sort("Int"))) =>
//    }
//  }
//
//  @Test def testSortLattice {
//    val d = Module("TEST", Set(testSyntaxModule), Set(
//      Production(Sort("Exp"), Seq(NonTerminal(Sort("Int"))))))
//
//    println(d.subsorts)
//  }
//
//  //      assertEquals(Set(),
//  //      nonTerminalWithUndefinedSort(dCorrect))
//  //    assertEquals(Set(NonTerminal(Sort("Exp"))),
//  //      nonTerminalWithUndefinedSort(dIncorrect))
//  //    assertEquals(Set(NonTerminal(Sort("Int"))),
//  //      nonTerminalWithUndefinedSort(dIncorrect1))
//
//  @Test def testVisitor() = {
//    val d = Definition(Set(), Set(
//      Module("TEST", Set(testSyntaxModule), Set(
//        Import("TEST-SYNTAX"),
//        Production(Sort("Exp"), Seq(NonTerminal(Sort("Int"))))))))
//
//    object myVisitor extends AbstractVisitor {
//      val mentionedSorts = collection.mutable.Set[Sort]()
//      def visit(s: Sort) = { mentionedSorts += s }
//    }
//    myVisitor(d)
//
//    assertEquals(Set(Sort("Exp"), Sort("Int")), myVisitor.mentionedSorts)
//  }
//}
