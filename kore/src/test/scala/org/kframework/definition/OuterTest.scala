// Copyright (c) K Team. All Rights Reserved.

package org.kframework.definition

import org.junit.{Assert, Test}
import org.kframework.attributes.Att
import org.kframework.kore.ADT.KToken
import org.kframework.kore.KORE.Sort
import org.kframework.kore.KORE.KLabel

class OuterTest {
  @Test def isPrefixTest(): Unit = {
    val sort = Sort("foo")
    val nt = NonTerminal(sort, None)
    val prod1 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("("), nt, Terminal(")")), Att.empty)
    Assert.assertTrue(prod1.isPrefixProduction)
    val prod2 = Production(Seq(), sort, Seq(Terminal("foo")), Att.empty)
    Assert.assertFalse(prod2.isPrefixProduction)
    val prod3 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("(")), Att.empty)
    Assert.assertFalse(prod3.isPrefixProduction)
    val prod4 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("("), nt), Att.empty)
    Assert.assertFalse(prod4.isPrefixProduction)
    val prod5 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("("), nt, Terminal(",")), Att.empty)
    Assert.assertFalse(prod5.isPrefixProduction)
    val prod6 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("("), nt, Terminal(","), nt), Att.empty)
    Assert.assertFalse(prod6.isPrefixProduction)
    val prod7 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("("), nt, Terminal(","), Terminal(")")), Att.empty)
    Assert.assertFalse(prod7.isPrefixProduction)
    val prod8 = Production(Seq(), sort, Seq(Terminal("foo"), Terminal("("), Terminal(")")), Att.empty)
    Assert.assertTrue(prod8.isPrefixProduction)
    val prod9 = Production(Seq(), sort, Seq(Terminal("("), Terminal(")")), Att.empty)
    Assert.assertTrue(prod9.isPrefixProduction)
    val prod10 = Production(Seq(), sort, Seq(Terminal("("), nt, Terminal(","), nt, Terminal(")")), Att.empty)
    Assert.assertTrue(prod10.isPrefixProduction)
  }

  @Test def recordProductions1(): Unit = {
    val uid = UidProvider("")
    val sort1 = Sort("foo1")
    val sort2 = Sort("foo2")
    val nt1 = NonTerminal(sort1, Some("bar"))
    val nt2 = NonTerminal(sort2, Some("baz"))
    val prod = Production(Seq(), sort1, Seq(Terminal("foo"), Terminal("("), nt1, Terminal(","), nt2, Terminal(")")), Att.empty)
    val newAtt = Att.empty.add(Att.RECORD_PRD, classOf[Production], prod)
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
    val prod = Production(Seq(), sort1, Seq(Terminal("foo"), Terminal("("), nt1, Terminal(","), nt2, Terminal(")")), Att.empty)
    val newAtt = Att.empty.add(Att.RECORD_PRD, classOf[Production], prod)
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
    val prod = Production(Seq(), sort1, Seq(Terminal("foo"), Terminal("("), nt1, Terminal(","), nt2, Terminal(")")), Att.empty)
    val newAtt = Att.empty.add(Att.RECORD_PRD, classOf[Production], prod)
    val records = prod.recordProductions(uid)
    Assert.assertEquals(1, records.size)
    Assert.assertEquals(Set(
      Production(Seq(), sort1, Seq(Terminal("foo"), Terminal("("), Terminal("..."), Terminal(")")), newAtt)
    ), records)
  }

  @Test def klabelAttEquality(): Unit = {
    val prod1 = Production(Some(KLabel("foo")), Seq(), Sort("Foo"), Seq(), Att.empty.add(Att.KLABEL, "foo"))
    val prod2 = Production(Some(KLabel("foo")), Seq(), Sort("Foo"), Seq(), Att.empty.add(Att.KLABEL, "bar"))
    Assert.assertNotEquals(prod1, prod2)
  }

  // Asserts that S1 < S2 < ... < Sn
  // Likewise, Sn > Sn-1 > ... > S1
  def assertOrdering(sentences: Sentence*): Unit = {
    val ord = Ordering[Sentence]
    for (remaining <- sentences.tails.filter(_.nonEmpty)) {
      val head = remaining.head
      for (sentence <- remaining.tail) {
        Assert.assertTrue(ord.compare(head, sentence) < 0)
        Assert.assertTrue(ord.compare(sentence, head) > 0)
      }
    }
  }

  @Test def sentenceOrdering(): Unit = {
    val sortA = Sort("A")
    val sortB = Sort("B")
    val sortC = Sort("C")

    val ktokenA = KToken("A", sortA)
    val ktokenB = KToken("B", sortA)
    val ktokenC = KToken("C", sortA)

    val tagA = Tag("A")
    val tagB = Tag("B")
    val tagC = Tag("C")

    val syntaxSort1 = SyntaxSort(Seq(sortA, sortC), sortA)
    val syntaxSort2 = SyntaxSort(Seq(sortA, sortC), sortB)
    val syntaxSort3 = SyntaxSort(Seq(sortB, sortC), sortA)
    assertOrdering(syntaxSort1, syntaxSort2, syntaxSort3)

    val synonym1 = SortSynonym(sortA, sortA)
    val synonym2 = SortSynonym(sortA, sortB)
    val synonym3 = SortSynonym(sortB, sortC)
    assertOrdering(synonym1, synonym2, synonym3)

    val lexical1 = SyntaxLexical("A", "A")
    val lexical2 = SyntaxLexical("A", "B")
    val lexical3 = SyntaxLexical("B", "A")
    assertOrdering(lexical1, lexical2, lexical3)

    val production1 = Production(Seq(), sortA, Seq(), Att.empty)
    val production2 = Production(KLabel("A"), Seq(), sortA, Seq(), Att.empty)
    val production3 = Production(KLabel("B"), Seq(), sortA, Seq(), Att.empty)
    assertOrdering(production1, production2, production3)

    val syntaxAssoc1 = SyntaxAssociativity(Associativity.Left, Set(tagA))
    val syntaxAssoc2 = SyntaxAssociativity(Associativity.Left, Set(tagB))
    val syntaxAssoc3 = SyntaxAssociativity(Associativity.Right, Set(tagA))
    assertOrdering(syntaxAssoc1, syntaxAssoc2, syntaxAssoc3)

    val syntaxPriority1 = SyntaxPriority(Seq(Set(tagB, tagA)))
    val syntaxPriority2 = SyntaxPriority(Seq(Set(tagA, tagB, tagC), Set(tagB)))
    val syntaxPriority3 = SyntaxPriority(Seq(Set(tagA, tagB, tagC), Set(tagC)))
    val syntaxPriority4 = SyntaxPriority(Seq(Set(tagA, tagC, tagC), Set(tagB)))
    val syntaxPriority5 = SyntaxPriority(Seq(Set(tagB)))
    assertOrdering(syntaxPriority1, syntaxPriority2, syntaxPriority3, syntaxPriority4, syntaxPriority5)

    val contextAlias1 = ContextAlias(ktokenA, ktokenA)
    val contextAlias2 = ContextAlias(ktokenA, ktokenB)
    val contextAlias3 = ContextAlias(ktokenB, ktokenB)
    assertOrdering(contextAlias1, contextAlias2, contextAlias3)

    val context1 = Context(ktokenA, ktokenA)
    val context2 = Context(ktokenA, ktokenB)
    val context3 = Context(ktokenB, ktokenA)
    assertOrdering(context1, context2, context3)

    val rule1 = Rule(ktokenA, ktokenA, ktokenA)
    val rule2 = Rule(ktokenA, ktokenA, ktokenB)
    val rule3 = Rule(ktokenA, ktokenA, ktokenC)
    val rule4 = Rule(ktokenA, ktokenB, ktokenA)
    val rule5 = Rule(ktokenB, ktokenA, ktokenA)
    assertOrdering(rule1, rule2, rule3, rule4, rule5)

    val claim1 = Claim(ktokenA, ktokenA, ktokenA)
    val claim2 = Claim(ktokenA, ktokenA, ktokenB)
    val claim3 = Claim(ktokenA, ktokenA, ktokenC)
    val claim4 = Claim(ktokenA, ktokenB, ktokenA)
    val claim5 = Claim(ktokenB, ktokenA, ktokenA)
    assertOrdering(claim1, claim2, claim3, claim4, claim5)

    assertOrdering(
      syntaxSort1,
      synonym1,
      lexical1,
      production1,
      syntaxAssoc1,
      syntaxPriority1,
      contextAlias1,
      context1,
      rule1,
      claim1)
  }
}
