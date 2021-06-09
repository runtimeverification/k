// Copyright (c) 2016-2019 K Team. All Rights Reserved.

package org.kframework.definition

import org.junit.{Assert, Test}
import org.kframework.kore.KORE.Att
import org.kframework.kore.KORE.Sort
import org.kframework.kore.KORE.KLabel

class OuterTest {
  @Test def isPrefixTest(): Unit = {
    val sort = Sort("foo")
    val nt = NonTerminal(sort, None)
    val prod1 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("("), nt, Terminal(")")), Att)
    Assert.assertTrue(prod1.isPrefixProduction)
    val prod2 = Production(Seq(), sort, Seq(Terminal("foo")), Att)
    Assert.assertFalse(prod2.isPrefixProduction)
    val prod3 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("(")), Att)
    Assert.assertFalse(prod3.isPrefixProduction)
    val prod4 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("("), nt), Att)
    Assert.assertFalse(prod4.isPrefixProduction)
    val prod5 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("("), nt, Terminal(",")), Att)
    Assert.assertFalse(prod5.isPrefixProduction)
    val prod6 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("("), nt, Terminal(","), nt), Att)
    Assert.assertFalse(prod6.isPrefixProduction)
    val prod7 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("("), nt, Terminal(","), Terminal(")")), Att)
    Assert.assertFalse(prod7.isPrefixProduction)
    val prod8 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("("), Terminal(")")), Att)
    Assert.assertTrue(prod8.isPrefixProduction)
    val prod9 = Production(Seq(), sort, Seq(Terminal("("), Terminal(")")), Att)
    Assert.assertTrue(prod9.isPrefixProduction)
    val prod10 = Production(Seq(), sort, Seq(Terminal("("), nt, Terminal(","), nt, Terminal(")")), Att)
    Assert.assertTrue(prod10.isPrefixProduction)
  }

  @Test def recordProductions1(): Unit = {
    val uid = UidProvider("")
    val sort1 = Sort("foo1")
    val sort2 = Sort("foo2")
    val nt1 = NonTerminal(sort1, Some("bar"))
    val nt2 = NonTerminal(sort2, Some("baz"))
    val prod = Production(Seq(), sort1, Seq(Terminal("foo"), Terminal("("), nt1, Terminal(","), nt2, Terminal(")")), Att)
    val newAtt = Att.add("recordPrd", classOf[Production], prod)
    val records = prod.recordProductions(uid)
    Assert.assertEquals(7, records.size)
    Assert.assertEquals(Set(
      Production(Seq(), sort1, Seq(Terminal("foo"), Terminal("("), Terminal("..."), NonTerminal(Sort("foo-+1"), None), Terminal(")")), newAtt), // main
      Production(Seq(), Sort("foo-+1"), Seq(Terminal("")), newAtt), // empty
      Production(Seq(), Sort("foo-+1"), Seq(NonTerminal(Sort("foo-+1Ne"), None)), newAtt), // subsort
      Production(Seq(), Sort("foo-+1Ne"), Seq(NonTerminal(Sort("foo-+1Ne"), None), Terminal(","), NonTerminal(Sort("foo-+1Item"), None)), newAtt), // repeat
      Production(Seq(), Sort("foo-+1Ne"), Seq(NonTerminal(Sort("foo-+1Item"), None)), newAtt), // subsort2
      Production(Seq(), Sort("foo-+1Item"), Seq(Terminal("bar"), Terminal(":"), NonTerminal(sort1, None)), newAtt), // item
      Production(Seq(), Sort("foo-+1Item"), Seq(Terminal("baz"), Terminal(":"), NonTerminal(sort2, None)), newAtt), // item
    ), records)
  }

  @Test def recordProductions2(): Unit = {
    val uid = UidProvider("")
    val sort1 = Sort("foo1")
    val sort2 = Sort("foo2")
    val nt1 = NonTerminal(sort1, None)
    val nt2 = NonTerminal(sort2, Some("baz"))
    val prod = Production(Seq(), sort1, Seq(Terminal("foo"), Terminal("("), nt1, Terminal(","), nt2, Terminal(")")), Att)
    val newAtt = Att.add("recordPrd", classOf[Production], prod)
    val records = prod.recordProductions(uid)
    Assert.assertEquals(2, records.size)
    Assert.assertEquals(Set(
      Production(Seq(), sort1, Seq(Terminal("foo"), Terminal("("), Terminal("..."), Terminal(")")), newAtt),
      Production(Seq(), sort1, Seq(Terminal("foo"), Terminal("("), Terminal("..."), Terminal("baz"), Terminal(":"), nt2, Terminal(")")), newAtt),
    ), records)
  }

  @Test def recordProductions3(): Unit = {
    val uid = UidProvider("")
    val sort1 = Sort("foo1")
    val sort2 = Sort("foo2")
    val nt1 = NonTerminal(sort1, None)
    val nt2 = NonTerminal(sort2, None)
    val prod = Production(Seq(), sort1, Seq(Terminal("foo"), Terminal("("), nt1, Terminal(","), nt2, Terminal(")")), Att)
    val newAtt = Att.add("recordPrd", classOf[Production], prod)
    val records = prod.recordProductions(uid)
    Assert.assertEquals(1, records.size)
    Assert.assertEquals(Set(
      Production(Seq(), sort1, Seq(Terminal("foo"), Terminal("("), Terminal("..."), Terminal(")")), newAtt)
    ), records)
  }

  @Test def klabelAttEquality(): Unit = {
    val prod1 = Production(Some(KLabel("foo")), Seq(), Sort("Foo"), Seq(), Att.add("klabel", "foo"))
    val prod2 = Production(Some(KLabel("foo")), Seq(), Sort("Foo"), Seq(), Att.add("klabel", "bar"))
    Assert.assertNotEquals(prod1, prod2)
  }
}
