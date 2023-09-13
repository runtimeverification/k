// Copyright (c) K Team. All Rights Reserved.

package org.kframework.parser.kore.parser

import org.junit.{Assert, Test}

import org.kframework.parser.kore.implementation.{DefaultBuilders => b}

class TextToKoreTest {
  @Test def testMultiOr(): Unit = {
    val kore1 = "\\left-assoc{}(\\or{SortInt{}}(\\dv{SortInt{}}(\"1\"), \\dv{SortInt{}}(\"2\"), \\dv{SortInt{}}(\"3\")))"
    val parser = new TextToKore()
    val ast1 = parser.parsePattern(kore1)
    val int = b.CompoundSort("SortInt", Seq())
    Assert.assertEquals(b.Or(int, b.Or(int, b.DomainValue(int, "1"), b.DomainValue(int, "2")), b.DomainValue(int, "3")), ast1)

    val kore2 = "\\right-assoc{}(\\or{SortInt{}}(\\dv{SortInt{}}(\"1\"), \\dv{SortInt{}}(\"2\"), \\dv{SortInt{}}(\"3\")))"
    val ast2 = parser.parsePattern(kore2)
    Assert.assertEquals(b.Or(int, b.DomainValue(int, "1"), b.Or(int, b.DomainValue(int, "2"), b.DomainValue(int, "3"))), ast2)
  }

  @Test def testMultiAnd(): Unit = {
    val kore1 = "\\left-assoc{}(\\and{SortInt{}}(\\dv{SortInt{}}(\"1\"), \\dv{SortInt{}}(\"2\"), \\dv{SortInt{}}(\"3\")))"
    val parser = new TextToKore()
    val ast1 = parser.parsePattern(kore1)
    val int = b.CompoundSort("SortInt", Seq())
    Assert.assertEquals(b.And(int, b.And(int, b.DomainValue(int, "1"), b.DomainValue(int, "2")), b.DomainValue(int, "3")), ast1)

    val kore2 = "\\right-assoc{}(\\and{SortInt{}}(\\dv{SortInt{}}(\"1\"), \\dv{SortInt{}}(\"2\"), \\dv{SortInt{}}(\"3\")))"
    val ast2 = parser.parsePattern(kore2)
    Assert.assertEquals(b.And(int, b.DomainValue(int, "1"), b.And(int, b.DomainValue(int, "2"), b.DomainValue(int, "3"))), ast2)
  }

  @Test def testAssocApplication(): Unit = {
    val parser = new TextToKore()
    val int = b.CompoundSort("SortInt", Seq())

    val koreLeft = "\\left-assoc{}(Lbl'Unds'Map'Unds{}(\\dv{SortInt{}}(\"1\"), \\dv{SortInt{}}(\"1\")))"
    val astLeft = parser.parsePattern(koreLeft)
    Assert.assertEquals(b.Application(b.SymbolOrAlias("Lbl'Unds'Map'Unds", Seq()), Seq(b.DomainValue(int, "1"), b.DomainValue(int, "1"))), astLeft)

    val koreRight = "\\right-assoc{}(Lbl'Unds'Map'Unds{}(\\dv{SortInt{}}(\"1\"), \\dv{SortInt{}}(\"1\")))"
    val astRight = parser.parsePattern(koreRight)
    Assert.assertEquals(b.Application(b.SymbolOrAlias("Lbl'Unds'Map'Unds", Seq()), Seq(b.DomainValue(int, "1"), b.DomainValue(int, "1"))), astRight)
  }

}
