// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.backend.kore

import org.kframework.parser.kore.implementation.{DefaultBuilders => B}

import org.junit.Test
import org.junit.Assert._

class NoAppendIT extends KoreTest {

  @Test def test() {
    val axioms = this.axioms("module TEST imports K-EQUAL imports DEFAULT-STRATEGY configuration <k> $PGM:K </k> <s/> endmodule")
    for (axiom <- axioms) {
      val rewrite = getRewrite(axiom)
      if (rewrite.isDefined) {
        val lhs = rewrite.get.getLeftHandSide
        for (pat <- lhs) {
          assertFalse(symbols(pat).contains(B.SymbolOrAlias("append", Seq())))
        }
      }
    }
  }
}
