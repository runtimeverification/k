// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile

import collection._
import org.kframework.attributes.Att
import org.kframework.definition._
import org.kframework.kore.KORE.Sort
import org.kframework.Collections
import scala.collection.immutable.Iterable

object AddBottomSortForListsWithIdenticalLabels extends Function[Module, Module] {
  val singleton = this

  override def apply(m: Module) = {
    val theAdditionalSubsortingProductionsSets: Iterable[Set[Sentence]] = UserList
      .apply(m.sentences)
      .groupBy(l => l.klabel)
      .map { case (klabel, userListInfo) =>
        val minimalSorts = m.subsorts.minimal(Collections.iterable(userListInfo.map(li => li.sort)))
        if (minimalSorts.size > 1) {
          val newBottomSort = Sort("GeneratedListBottom{" + klabel.name.replace("|", "") + "}")

          Set[Sentence]()
            .|(
              Collections
                .immutable(minimalSorts)
                .map(s => Production(Seq(), s, Seq(NonTerminal(newBottomSort, None)), Att.empty))
            )
            .+(SyntaxSort(Seq(), newBottomSort, Att.empty))
            .+(
              Production(
                userListInfo.head.pTerminator.klabel.get,
                Seq(),
                newBottomSort,
                Seq(Terminal(".GeneratedListBottom")),
                Att.empty.add(Att.UNPARSE_AVOID)
              )
            )
        } else {
          Set[Sentence]()
        }
      }

    val theAdditionalSubsortingProductions = theAdditionalSubsortingProductionsSets.flatten

    if (theAdditionalSubsortingProductions.nonEmpty)
      Module(m.name, m.imports, m.localSentences ++ theAdditionalSubsortingProductions, m.att)
    else
      m
  }
}
