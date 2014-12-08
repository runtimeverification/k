package org.kframework.tiny

import org.kframework.kore._
import org.junit.Test
import KORE._

object Optimize {
  def apply(t: K): K = {
    val optimizations = KRewrite('List(), 'List())

    t.search(optimizations) match {
      case s if s.size == 0 => throw new RuntimeException("Could not find an optimization solution for the given term.")
      case s if s.size == 1 => s.head.asInstanceOf[K]
      case s if s.size > 1 => throw new RuntimeException("There is some issue. More than one optimization solution.")
    }
  }
}

class OptimizerTest {
  @Test
  def simple() {
    println(Optimize('List()))
  }
}
