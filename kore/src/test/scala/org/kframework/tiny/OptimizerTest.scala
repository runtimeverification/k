package org.kframework.tiny

import org.kframework.kore._
import org.junit.Test
import KORE._
import org.kframework.kore.outer._
import org.junit.Ignore

object Optimize {
  def apply(t: K): K = {
    val X = KVariable("X")
    val optimizations = Rule(Anywhere(KRewrite('Set(X), 'SetOptimized(X))))
    import Strategy._

    val repeatOptimizations = repeat(optimizations)

    repeatOptimizations(t) match {
      case s if s.size == 0 => throw new RuntimeException("Could not find an optimization solution for the given term.")
      case s if s.size == 1 => s.head.asInstanceOf[K]
      case s if s.size > 1 =>
        System.err.println(s mkString "\n")
        throw new RuntimeException("There is some issue. More than one optimization solution.")
    }
  }
}

class OptimizerTest {
  val d = Definition(Set(),
    Set(Module("TEST",
      Set(SyntaxProduction(Sort("Foo"),
        List(Terminal("Bar")))))))

  @Test
  def simple() {
    println(Optimize(Up(d)))
  }
}
