// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.backend.kore

import org.junit.Assert._
import org.junit.Test
import org.kframework.parser.kore._

class ClaimAttributes extends KoreTest {

  @Test def test() {
    val definition = this.kompile("module TEST [all-path] configuration <k> $PGM:K </k> syntax Exp ::= \"a\" | \"b\" " +
      "rule a => b [one-path] " +
      "rule a => b [all-path] " +
      "rule a => b " +
      "endmodule")
    val claims = this.claims(definition)
    assertEquals(3, claims.size)
    var one_path = 0
    var all_path = 0
    for (claim <- claims)  {
      if (this.hasAttribute(claim.att, "one-path")) {
        one_path=one_path+1;
        assertEquals("weakExistsFinally", claim.pattern.asInstanceOf[Implies]._2.asInstanceOf[Application].head.ctr);
      } else {
        assertEquals("weakAlwaysFinally", claim.pattern.asInstanceOf[Implies]._2.asInstanceOf[Application].head.ctr);
        all_path=all_path+1;
      }
    }
    assertEquals(1, one_path);
    assertEquals(2, all_path);
  }
}
