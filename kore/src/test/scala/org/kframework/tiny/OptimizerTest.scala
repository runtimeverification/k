package org.kframework.tiny

import org.kframework.koreimplementation._
import org.junit.Test
import KORE._
import org.kframework.definition._
import org.junit.Ignore

class OptimizerTest {
  val d = Definition(Set(),
    Set(Module("TEST", Set(),
      Set(SyntaxProduction(Sort("Foo"),
        List(Terminal("Bar")))))))

  @Test
  def simple() {
    println(Optimize(Up(d)))
  }
}
