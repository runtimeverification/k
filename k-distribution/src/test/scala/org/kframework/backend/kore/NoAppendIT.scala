// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.backend.kore

import com.runtimeverification.k.kore.implementation.{ DefaultBuilders => B }
import org.junit.Assert._
import org.junit.Test
import scala.collection.immutable

class NoAppendIT extends KoreTest {

  @Test def test() {
    val axioms = this.axioms(
      "module TEST imports K-EQUAL configuration <k> $PGM:K </k> endmodule"
    )
    for (axiom <- axioms) {
      val rewrite = getRewrite(axiom)
      if (rewrite.isDefined) {
        val lhs = rewrite.get.getLeftHandSide
        for (pat <- lhs)
          assertFalse(symbols(pat).contains(B.SymbolOrAlias("append", immutable.Seq())))
      }
    }
  }
}
