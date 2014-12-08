package org.kframework.kore.outer

import org.junit.Test
import org.kframework.kore.Sort

abstract class Visitor {
  def visit(o: Product) = {

  }
}

import collection.immutable._

class VisitTest {
  @Test def play {
    val dCorrect = Definition(Set(),
      Set(
        Module("TEST-SYNTAX", Set(
          SyntaxSort(Sort("Int")))),
        Module("TEST", Set(
          Import("TEST-SYNTAX"),
          SyntaxProduction(Sort("Exp"), Seq(NonTerminal(Sort("Int"))))))))

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

    println(nonTerminalWithUndefinedSort(dCorrect))
    println(nonTerminalWithUndefinedSort(dIncorrect))
    println(nonTerminalWithUndefinedSort(dIncorrect1))
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
}
