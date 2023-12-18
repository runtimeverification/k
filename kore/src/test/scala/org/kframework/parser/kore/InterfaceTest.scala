// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework.parser.kore

import org.junit.Assert
import org.junit.Test
import org.kframework.parser.kore.implementation.{ DefaultBuilders => b }

class InterfaceTest {

  @Test def patternOrdering(): Unit = {
    val sortA = b.CompoundSort("A", Seq())
    val sortB = b.CompoundSort("B", Seq())
    val sortC = b.CompoundSort("C", Seq())

    val dvA = b.DomainValue(sortA, "A")
    val dvB = b.DomainValue(sortB, "B")
    val dvC = b.DomainValue(sortC, "C")

    val varA = b.Variable("A", sortA)
    val varB = b.Variable("B", sortB)
    val varC = b.Variable("C", sortC)

    val symbolA = b.SymbolOrAlias("A", Seq())
    val symbolB = b.SymbolOrAlias("B", Seq())
    val symbolC = b.SymbolOrAlias("C", Seq())

    val appA = b.Application(symbolA, Seq(dvA, varA))
    val appB = b.Application(symbolB, Seq(dvB, varB))
    val appC = b.Application(symbolC, Seq(dvC, varC))

    val topA = b.Top(sortA)
    val topB = b.Top(sortB)
    val topC = b.Top(sortC)

    val bottomA = b.Bottom(sortA)
    val bottomB = b.Bottom(sortB)
    val bottomC = b.Bottom(sortC)

    val andA = b.And(sortA, Seq(topA, bottomA))
    val andB = b.And(sortB, Seq(topB, bottomB))
    val andC = b.And(sortC, Seq(topC, bottomC))

    val orA = b.Or(sortA, Seq(topA, bottomA))
    val orB = b.Or(sortB, Seq(topB, bottomB))
    val orC = b.Or(sortC, Seq(topC, bottomC))

    val notA = b.Not(sortA, topA)
    val notB = b.Not(sortB, topB)
    val notC = b.Not(sortC, topC)

    val impliesA = b.Implies(sortA, topA, bottomA)
    val impliesB = b.Implies(sortB, topB, bottomB)
    val impliesC = b.Implies(sortC, topC, bottomC)

    val iffA = b.Iff(sortA, topA, bottomA)
    val iffB = b.Iff(sortB, topB, bottomB)
    val iffC = b.Iff(sortC, topC, bottomC)

    val existsA = b.Exists(sortA, varA, appA)
    val existsB = b.Exists(sortB, varB, appB)
    val existsC = b.Exists(sortC, varC, appC)

    val forallA = b.Forall(sortA, varA, appA)
    val forallB = b.Forall(sortB, varB, appB)
    val forallC = b.Forall(sortC, varC, appC)

    val ceilA = b.Ceil(sortA, sortA, appA)
    val ceilB = b.Ceil(sortB, sortB, appB)
    val ceilC = b.Ceil(sortC, sortC, appC)

    val floorA = b.Floor(sortA, sortA, appA)
    val floorB = b.Floor(sortB, sortB, appB)
    val floorC = b.Floor(sortC, sortC, appC)

    val rewrites1 = b.Rewrites(sortA, appA, varA)
    val rewrites2 = b.Rewrites(sortB, appB, varB)
    val rewrites3 = b.Rewrites(sortC, appC, varC)
    val rewrites4 = b.Rewrites(sortA, varA, appA)
    val rewrites5 = b.Rewrites(sortB, varB, appB)
    val rewrites6 = b.Rewrites(sortC, varC, appC)
    val rewrites7 = b.Rewrites(sortA, varA, dvA)
    val rewrites8 = b.Rewrites(sortB, varB, dvB)
    val rewrites9 = b.Rewrites(sortC, varC, dvC)

    val equalsA = b.Equals(sortA, sortA, appA, appA)
    val equalsB = b.Equals(sortB, sortB, appB, appB)
    val equalsC = b.Equals(sortC, sortC, appC, appC)

    val memA = b.Mem(sortA, sortA, appA, appA)
    val memB = b.Mem(sortB, sortB, appB, appB)
    val memC = b.Mem(sortC, sortC, appC, appC)

    val strA = b.StringLiteral("A")
    val strB = b.StringLiteral("B")
    val strC = b.StringLiteral("C")

    val sentenceList = List(
      varA,
      varB,
      varC,
      appA,
      appB,
      appC,
      topA,
      topB,
      topC,
      bottomA,
      bottomB,
      bottomC,
      andA,
      andB,
      andC,
      orA,
      orB,
      orC,
      notA,
      notB,
      notC,
      impliesA,
      impliesB,
      impliesC,
      iffA,
      iffB,
      iffC,
      existsA,
      existsB,
      existsC,
      forallA,
      forallB,
      forallC,
      ceilA,
      ceilB,
      ceilC,
      floorA,
      floorB,
      floorC,
      rewrites4,
      rewrites7,
      rewrites1,
      rewrites5,
      rewrites8,
      rewrites2,
      rewrites6,
      rewrites9,
      rewrites3,
      equalsA,
      equalsB,
      equalsC,
      memA,
      memB,
      memC,
      dvA,
      dvB,
      dvC,
      strA,
      strB,
      strC
    )
    checkOrdering(sentenceList)
  }

  def checkOrdering(sentences: List[Pattern]): Unit = {
    val ord = Ordering[Pattern]
    for (remaining <- sentences.tails.filter(_.nonEmpty)) {
      val head = remaining.head
      Assert.assertTrue(ord.compare(head, head) == 0)
      for (sentence <- remaining.tail) {
        Assert.assertTrue(ord.compare(head, sentence) < 0)
        Assert.assertTrue(ord.compare(sentence, head) > 0)
      }
    }
  }
}
