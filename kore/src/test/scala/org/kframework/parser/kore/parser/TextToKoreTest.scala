// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework.parser.kore.parser

import org.junit.Assert
import org.junit.Test
import org.kframework.parser.kore.implementation.{ DefaultBuilders => b }

class TextToKoreTest {
  @Test def testMultiOr(): Unit = {
    val kore1 =
      "\\or{SortInt{}}(\\dv{SortInt{}}(\"1\"), \\dv{SortInt{}}(\"2\"), \\dv{SortInt{}}(\"3\"))"
    val parser = new TextToKore()
    val ast1   = parser.parsePattern(kore1)
    val int    = b.CompoundSort("SortInt", Seq())
    Assert.assertEquals(
      b.Or(int, Seq(b.DomainValue(int, "1"), b.DomainValue(int, "2"), b.DomainValue(int, "3"))),
      ast1
    )
  }

  @Test def testMultiAnd(): Unit = {
    val kore1 =
      "\\and{SortInt{}}(\\dv{SortInt{}}(\"1\"), \\dv{SortInt{}}(\"2\"), \\dv{SortInt{}}(\"3\"))"
    val parser = new TextToKore()
    val ast1   = parser.parsePattern(kore1)
    val int    = b.CompoundSort("SortInt", Seq())
    Assert.assertEquals(
      b.And(int, Seq(b.DomainValue(int, "1"), b.DomainValue(int, "2"), b.DomainValue(int, "3"))),
      ast1
    )
  }

  @Test def testAssocApplication(): Unit = {
    val parser = new TextToKore()
    val int    = b.CompoundSort("SortInt", Seq())

    val koreLeft =
      "\\left-assoc{}(Lbl'Unds'Map'Unds{}(\\dv{SortInt{}}(\"1\"), \\dv{SortInt{}}(\"1\")))"
    val astLeft = parser.parsePattern(koreLeft)
    Assert.assertEquals(
      b.Application(
        b.SymbolOrAlias("Lbl'Unds'Map'Unds", Seq()),
        Seq(b.DomainValue(int, "1"), b.DomainValue(int, "1"))
      ),
      astLeft
    )

    val koreRight =
      "\\right-assoc{}(Lbl'Unds'Map'Unds{}(\\dv{SortInt{}}(\"1\"), \\dv{SortInt{}}(\"1\")))"
    val astRight = parser.parsePattern(koreRight)
    Assert.assertEquals(
      b.Application(
        b.SymbolOrAlias("Lbl'Unds'Map'Unds", Seq()),
        Seq(b.DomainValue(int, "1"), b.DomainValue(int, "1"))
      ),
      astRight
    )
  }

}
