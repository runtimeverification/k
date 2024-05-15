// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework.definition

import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import org.junit.runners.Parameterized.Parameters
import org.junit.Assert
import org.junit.Test
import org.kframework.attributes.Att
import org.kframework.definition.regex.RegexBody
import org.kframework.kore.ADT.KToken
import org.kframework.kore.KORE.KLabel
import org.kframework.kore.KORE.Sort
import scala.collection.immutable

class OuterTest {
  @Test def isPrefixTest(): Unit = {
    val sort = Sort("foo")
    val nt   = NonTerminal(sort, None)
    val prod1 =
      Production(
        immutable.Seq(),
        sort,
        immutable.Seq(Terminal("foo"), Terminal("("), nt, Terminal(")")),
        Att.empty
      )
    Assert.assertTrue(prod1.isPrefixProduction)
    val prod2 = Production(immutable.Seq(), sort, immutable.Seq(Terminal("foo")), Att.empty)
    Assert.assertFalse(prod2.isPrefixProduction)
    val prod3 =
      Production(immutable.Seq(), sort, immutable.Seq(Terminal("foo"), Terminal("(")), Att.empty)
    Assert.assertFalse(prod3.isPrefixProduction)
    val prod4 = Production(
      immutable.Seq(),
      sort,
      immutable.Seq(Terminal("foo"), Terminal("("), nt),
      Att.empty
    )
    Assert.assertFalse(prod4.isPrefixProduction)
    val prod5 =
      Production(
        immutable.Seq(),
        sort,
        immutable.Seq(Terminal("foo"), Terminal("("), nt, Terminal(",")),
        Att.empty
      )
    Assert.assertFalse(prod5.isPrefixProduction)
    val prod6 =
      Production(
        immutable.Seq(),
        sort,
        immutable.Seq(Terminal("foo"), Terminal("("), nt, Terminal(","), nt),
        Att.empty
      )
    Assert.assertFalse(prod6.isPrefixProduction)
    val prod7 = Production(
      immutable.Seq(),
      sort,
      immutable.Seq(Terminal("foo"), Terminal("("), nt, Terminal(","), Terminal(")")),
      Att.empty
    )
    Assert.assertFalse(prod7.isPrefixProduction)
    val prod8 =
      Production(
        immutable.Seq(),
        sort,
        immutable.Seq(Terminal("foo"), Terminal("("), Terminal(")")),
        Att.empty
      )
    Assert.assertTrue(prod8.isPrefixProduction)
    val prod9 =
      Production(immutable.Seq(), sort, immutable.Seq(Terminal("("), Terminal(")")), Att.empty)
    Assert.assertTrue(prod9.isPrefixProduction)
    val prod10 =
      Production(
        immutable.Seq(),
        sort,
        immutable.Seq(Terminal("("), nt, Terminal(","), nt, Terminal(")")),
        Att.empty
      )
    Assert.assertTrue(prod10.isPrefixProduction)
  }

  @Test def recordProductions1(): Unit = {
    val uid   = UidProvider("")
    val sort1 = Sort("foo1")
    val sort2 = Sort("foo2")
    val nt1   = NonTerminal(sort1, Some("bar"))
    val nt2   = NonTerminal(sort2, Some("baz"))
    val prod = Production(
      immutable.Seq(),
      sort1,
      immutable.Seq(Terminal("foo"), Terminal("("), nt1, Terminal(","), nt2, Terminal(")")),
      Att.empty
    )
    val newAtt  = Att.empty.add(Att.RECORD_PRD, classOf[Production], prod)
    val records = prod.recordProductions(uid)
    Assert.assertEquals(7, records.size)
    Assert.assertEquals(
      Set(
        Production(
          immutable.Seq(),
          sort1,
          immutable.Seq(
            Terminal("foo"),
            Terminal("("),
            Terminal("..."),
            NonTerminal(Sort("foo-+1"), None),
            Terminal(")")
          ),
          newAtt
        ),                                                                                // main
        Production(immutable.Seq(), Sort("foo-+1"), immutable.Seq(Terminal("")), newAtt), // empty
        Production(
          immutable.Seq(),
          Sort("foo-+1"),
          immutable.Seq(NonTerminal(Sort("foo-+1Ne"), None)),
          newAtt
        ), // subsort
        Production(
          immutable.Seq(),
          Sort("foo-+1Ne"),
          immutable.Seq(
            NonTerminal(Sort("foo-+1Ne"), None),
            Terminal(","),
            NonTerminal(Sort("foo-+1Item"), None)
          ),
          newAtt
        ), // repeat
        Production(
          immutable.Seq(),
          Sort("foo-+1Ne"),
          immutable.Seq(NonTerminal(Sort("foo-+1Item"), None)),
          newAtt
        ), // subsort2
        Production(
          immutable.Seq(),
          Sort("foo-+1Item"),
          immutable.Seq(Terminal("bar"), Terminal(":"), NonTerminal(sort1, None)),
          newAtt
        ), // item
        Production(
          immutable.Seq(),
          Sort("foo-+1Item"),
          immutable.Seq(Terminal("baz"), Terminal(":"), NonTerminal(sort2, None)),
          newAtt
        ) // item
      ),
      records
    )
  }

  @Test def recordProductions2(): Unit = {
    val uid   = UidProvider("")
    val sort1 = Sort("foo1")
    val sort2 = Sort("foo2")
    val nt1   = NonTerminal(sort1, None)
    val nt2   = NonTerminal(sort2, Some("baz"))
    val prod = Production(
      immutable.Seq(),
      sort1,
      immutable.Seq(Terminal("foo"), Terminal("("), nt1, Terminal(","), nt2, Terminal(")")),
      Att.empty
    )
    val newAtt  = Att.empty.add(Att.RECORD_PRD, classOf[Production], prod)
    val records = prod.recordProductions(uid)
    Assert.assertEquals(2, records.size)
    Assert.assertEquals(
      Set(
        Production(
          immutable.Seq(),
          sort1,
          immutable.Seq(Terminal("foo"), Terminal("("), Terminal("..."), Terminal(")")),
          newAtt
        ),
        Production(
          immutable.Seq(),
          sort1,
          immutable.Seq(
            Terminal("foo"),
            Terminal("("),
            Terminal("..."),
            Terminal("baz"),
            Terminal(":"),
            nt2,
            Terminal(")")
          ),
          newAtt
        )
      ),
      records
    )
  }

  @Test def recordProductions3(): Unit = {
    val uid   = UidProvider("")
    val sort1 = Sort("foo1")
    val sort2 = Sort("foo2")
    val nt1   = NonTerminal(sort1, None)
    val nt2   = NonTerminal(sort2, None)
    val prod = Production(
      immutable.Seq(),
      sort1,
      immutable.Seq(Terminal("foo"), Terminal("("), nt1, Terminal(","), nt2, Terminal(")")),
      Att.empty
    )
    val newAtt  = Att.empty.add(Att.RECORD_PRD, classOf[Production], prod)
    val records = prod.recordProductions(uid)
    Assert.assertEquals(1, records.size)
    Assert.assertEquals(
      Set(
        Production(
          immutable.Seq(),
          sort1,
          immutable.Seq(Terminal("foo"), Terminal("("), Terminal("..."), Terminal(")")),
          newAtt
        )
      ),
      records
    )
  }

  @Test def klabelAttEquality(): Unit = {
    val prod1 =
      Production(
        Some(KLabel("foo")),
        immutable.Seq(),
        Sort("Foo"),
        immutable.Seq(),
        Att.empty.add(Att.KLABEL, "foo")
      )
    val prod2 =
      Production(
        Some(KLabel("foo")),
        immutable.Seq(),
        Sort("Foo"),
        immutable.Seq(),
        Att.empty.add(Att.KLABEL, "bar")
      )
    Assert.assertNotEquals(prod1, prod2)
  }

  // Create multiple versions of this sentence with attributes added
  def toSentenceAttList(sentence: Sentence): List[Sentence] = {
    val att1             = Att.empty.add(Att.ASSOC).add(Att.BAG)
    val att2             = Att.empty.add(Att.ASSOC).add(Att.CELL)
    val att3             = Att.empty.add(Att.BAG).add(Att.CELL)
    val att4             = Att.empty.add(Att.BAG).add(Att.HOOK, "A")
    val att5             = Att.empty.add(Att.BAG).add(Att.HOOK, "B")
    val att6             = Att.empty.add(Att.BAG).add(Att.LABEL, "A")
    val att7             = Att.empty.add(Att.BAG).add(Att.LABEL, "B")
    val att8             = Att.empty.add(Att.HOOK, "A").add(Att.LABEL, "B")
    val att9             = Att.empty.add(Att.HOOK, "B").add(Att.LABEL, "A")
    val sentenceWithAtt1 = sentence.withAtt(att1)
    val sentenceWithAtt2 = sentence.withAtt(att2)
    val sentenceWithAtt3 = sentence.withAtt(att3)
    val sentenceWithAtt4 = sentence.withAtt(att4)
    val sentenceWithAtt5 = sentence.withAtt(att5)
    val sentenceWithAtt6 = sentence.withAtt(att6)
    val sentenceWithAtt7 = sentence.withAtt(att7)
    val sentenceWithAtt8 = sentence.withAtt(att8)
    val sentenceWithAtt9 = sentence.withAtt(att9)

    List(
      sentenceWithAtt1,
      sentenceWithAtt2,
      sentenceWithAtt3,
      sentenceWithAtt4,
      sentenceWithAtt5,
      sentenceWithAtt6,
      sentenceWithAtt7,
      sentenceWithAtt8,
      sentenceWithAtt9
    )
  }

  // Asserts that S1 < S2 < ... < Sn
  // Likewise, Sn > ... > S2 > S1
  // And Sx = Sx
  def checkOrdering(sentences: List[Sentence]): Unit = {
    val ord = Ordering[Sentence]
    for (remaining <- sentences.tails.filter(_.nonEmpty)) {
      val head = remaining.head
      Assert.assertTrue(ord.compare(head, head) == 0)
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

    val syntaxSort1 = SyntaxSort(immutable.Seq(sortA, sortC), sortA)
    val syntaxSort2 = SyntaxSort(immutable.Seq(sortA, sortC), sortB)
    val syntaxSort3 = SyntaxSort(immutable.Seq(sortB, sortC), sortA)

    val synonym1 = SortSynonym(sortA, sortA)
    val synonym2 = SortSynonym(sortA, sortB)
    val synonym3 = SortSynonym(sortB, sortC)

    val lexical1 =
      SyntaxLexical("A", new RegexBody.Char('A'))
    val lexical2 =
      SyntaxLexical("A", new RegexBody.Char('B'))
    val lexical3 =
      SyntaxLexical("B", new RegexBody.Char('A'))

    val production1 = Production(immutable.Seq(), sortA, immutable.Seq(), Att.empty)
    val production2 = Production(KLabel("A"), immutable.Seq(), sortA, immutable.Seq(), Att.empty)
    val production3 = Production(KLabel("B"), immutable.Seq(), sortA, immutable.Seq(), Att.empty)

    val syntaxAssoc1 = SyntaxAssociativity(Associativity.Left, Set(tagA))
    val syntaxAssoc2 = SyntaxAssociativity(Associativity.Left, Set(tagB))
    val syntaxAssoc3 = SyntaxAssociativity(Associativity.Right, Set(tagA))

    val syntaxPriority1 = SyntaxPriority(immutable.Seq(Set(tagB, tagA)))
    val syntaxPriority2 = SyntaxPriority(immutable.Seq(Set(tagA, tagB, tagC), Set(tagB)))
    val syntaxPriority3 = SyntaxPriority(immutable.Seq(Set(tagA, tagB, tagC), Set(tagC)))
    val syntaxPriority4 = SyntaxPriority(immutable.Seq(Set(tagA, tagC, tagC), Set(tagB)))
    val syntaxPriority5 = SyntaxPriority(immutable.Seq(Set(tagB)))

    val contextAlias1 = ContextAlias(ktokenA, ktokenA)
    val contextAlias2 = ContextAlias(ktokenA, ktokenB)
    val contextAlias3 = ContextAlias(ktokenB, ktokenB)

    val context1 = Context(ktokenA, ktokenA)
    val context2 = Context(ktokenA, ktokenB)
    val context3 = Context(ktokenB, ktokenA)

    val rule1 = Rule(ktokenA, ktokenA, ktokenA)
    val rule2 = Rule(ktokenA, ktokenA, ktokenB)
    val rule3 = Rule(ktokenA, ktokenA, ktokenC)
    val rule4 = Rule(ktokenA, ktokenB, ktokenA)
    val rule5 = Rule(ktokenB, ktokenA, ktokenA)

    val claim1 = Claim(ktokenA, ktokenA, ktokenA)
    val claim2 = Claim(ktokenA, ktokenA, ktokenB)
    val claim3 = Claim(ktokenA, ktokenA, ktokenC)
    val claim4 = Claim(ktokenA, ktokenB, ktokenA)
    val claim5 = Claim(ktokenB, ktokenA, ktokenA)

    val sentenceList = List(
      syntaxSort1,
      syntaxSort2,
      syntaxSort3,
      synonym1,
      synonym2,
      synonym3,
      lexical1,
      lexical2,
      lexical3,
      production1,
      production2,
      production3,
      syntaxAssoc1,
      syntaxAssoc2,
      syntaxAssoc3,
      syntaxPriority1,
      syntaxPriority2,
      syntaxPriority3,
      syntaxPriority4,
      syntaxPriority5,
      contextAlias1,
      contextAlias2,
      contextAlias3,
      context1,
      context2,
      context3,
      rule1,
      rule2,
      rule3,
      rule4,
      rule5,
      claim1,
      claim2,
      claim3,
      claim4,
      claim5
    )

    val sentenceListWithAtts = sentenceList.flatMap(toSentenceAttList(_))

    checkOrdering(sentenceListWithAtts)
  }
}

@RunWith(classOf[Parameterized])
class DefaultFormatTest(
    production: Production,
    expected: String
) {
  @Test def test(): Unit =
    Assert.assertEquals(expected, production.defaultFormat)
}

object DefaultFormatTest {
  val S = Sort("S")

  @Parameters
  def data(): java.util.Collection[Array[Object]] = java.util.Arrays.asList(
    Array[Object](Production(Seq(), S, Seq(), Att.empty), ""),
    Array[Object](Production(Seq(), S, Seq(Terminal("foo")), Att.empty), "%1"),
    Array[Object](Production(Seq(), S, Seq(Terminal("foo"), Terminal("bar")), Att.empty), "%1 %2"),
    Array[Object](
      Production(Seq(), S, Seq(Terminal("foo"), Terminal("bar"), Terminal("baz")), Att.empty),
      "%1 %2 %3"
    ),
    Array[Object](
      Production(Seq(), S, Seq(Terminal("foo"), NonTerminal(S, None), Terminal("bar")), Att.empty),
      "%1 %2 %3"
    ),
    Array[Object](
      Production(Seq(), S, Seq(Terminal("foo"), Terminal("("), Terminal(")")), Att.empty),
      "%1 %2 %3"
    ),
    Array[Object](
      Production(
        Seq(),
        S,
        Seq(Terminal("foo"), Terminal("("), NonTerminal(S, None), Terminal(")")),
        Att.empty
      ),
      "%1 %2 %3 %4"
    ),
    Array[Object](
      Production(
        Seq(),
        S,
        Seq(Terminal("foo"), Terminal("("), NonTerminal(S, None), Terminal(")")),
        Att.empty
      ),
      "%1 %2 %3 %4"
    ),
    Array[Object](
      Production(
        Seq(),
        S,
        Seq(Terminal("foo"), Terminal("("), NonTerminal(S, Some("x")), Terminal(")")),
        Att.empty
      ),
      "%1 %2... x: %3 %4"
    ),
    Array[Object](
      Production(
        Seq(),
        S,
        Seq(
          Terminal("foo"),
          Terminal("("),
          NonTerminal(S, Some("x")),
          Terminal(","),
          NonTerminal(S, None),
          Terminal(")")
        ),
        Att.empty
      ),
      "%1 %2 %3 %4 %5 %6"
    ),
    Array[Object](
      Production(
        Seq(),
        S,
        Seq(
          Terminal("foo"),
          Terminal("("),
          NonTerminal(S, Some("x")),
          Terminal(","),
          NonTerminal(S, Some("y")),
          Terminal(")")
        ),
        Att.empty
      ),
      "%1 %2... x: %3 %4 y: %5 %6"
    )
  )
}
