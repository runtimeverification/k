package org.kframework.tinyimplementation

import org.kframework.koreimplementation._
import KORE._

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
        throw new RuntimeException("There is some issue. More than one optimization solution.")
    }
  }
}
