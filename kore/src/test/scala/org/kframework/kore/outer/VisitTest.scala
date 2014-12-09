package org.kframework.kore.outer

import org.junit.Test
import org.junit.Assert._
import org.kframework.kore.Sort

abstract class Visitor {
  def visit(o: Product) = {

  }
}

import collection.immutable._

class VisitTest {

  val dCorrect = Definition(Set(),
    Set(
      Module("TEST-SYNTAX", Set(
        SyntaxSort(Sort("Int")))),
      Module("TEST", Set(
        Import("TEST-SYNTAX"),
        SyntaxProduction(Sort("Exp"), Seq(NonTerminal(Sort("Int"))))))))

  @Test def play {

    val dIncorrect = Definition(Set(),
      Set(
        Module("TEST-SYNTAX", Set(
          SyntaxSort(Sort("Int")))),
        Module("TEST", Set(
          Import("TEST-SYNTAX"),
          SyntaxProduction(Sort("Int"), Seq(NonTerminal(Sort("Exp"))))))))

    val dIncorrect1 = Definition(Set(),
      Set(
        Module("TEST-SYNTAX", Set(
          SyntaxProduction(Sort("Exp"), Seq(NonTerminal(Sort("Int")))))),
        Module("TEST", Set(
          Import("TEST-SYNTAX"),
          SyntaxSort(Sort("Int"))))))

    assertEquals(Set(),
      nonTerminalWithUndefinedSort(dCorrect))
    assertEquals(Set(NonTerminal(Sort("Exp"))),
      nonTerminalWithUndefinedSort(dIncorrect))
    assertEquals(Set(NonTerminal(Sort("Int"))),
      nonTerminalWithUndefinedSort(dIncorrect1))
  }

  def nonTerminalWithUndefinedSort(implicit d: Definition): Set[NonTerminal] = {
    d.modules flatMap { m =>
      m.sentences flatMap {
        case SyntaxProduction(_, items, _) =>
          items collect { case nt: NonTerminal if !m.definedSorts.contains(nt.sort) => nt }
        case _ => Set()
      }
    }
  }

  @Test
  def testVisitor() = {
    object myVisitor extends AbstractVisitor {
      val mentionedSorts = collection.mutable.Set[Sort]()
      def visit(s: Sort) = { mentionedSorts += s }
    }
    myVisitor(dCorrect)

    assertEquals(Set(Sort("Exp"), Sort("Int")), myVisitor.mentionedSorts)
  }
}
