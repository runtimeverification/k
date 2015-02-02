package org.kframework.tiny

import net.sf.tweety.logics.pl.{syntax => tw}
import org.junit.Test

class LogicTest {
  @Test def foo {
    val f = new tw.Disjunction()
    val x: tw.PropositionalFormula = new tw.Disjunction(new tw.Proposition("a"), f)

    val n = new tw.Conjunction()

    println(x.toDnf)
    println(x.toCnf)
    println(x.toNnf)
    println(f)
    println(n)
    println(f.toDnf)
    println(n.toDnf)
  }
}
