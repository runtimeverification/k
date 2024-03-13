// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.backend.kore

import com.runtimeverification.k.kore.implementation.{ DefaultBuilders => B }
import org.junit.Assert._
import org.junit.Test

class NoAppendIT extends KoreTest {

  @Test def test() {
    val axioms = this.axioms(
      "module TEST imports K-EQUAL imports DEFAULT-STRATEGY configuration <k> $PGM:K </k> <s/> endmodule"
    )
    for (axiom <- axioms) {
      val rewrite = getRewrite(axiom)
      if (rewrite.isDefined) {
        val lhs = rewrite.get.getLeftHandSide
        for (pat <- lhs)
          assertFalse(symbols(pat).contains(B.SymbolOrAlias("append", Seq())))
      }
    }
  }
}
