package org.kframework.kore.compile

import org.kframework.attributes.Att
import org.kframework.definition.{Module, Rule}
import org.kframework.kore._

import scala.collection.JavaConverters._
import scala.collection.immutable.Iterable


class MergeRules(c: Constructors[K]) extends (Module => Module) {

  import c._

  val s = new ScalaSugar(c)

  import s._

  object ML {
    val and = KLabel("AND")
    val or = KLabel("OR")
    val True = KLabel("TRUE")()
    val False = KLabel("FALSE")()
  }

  import ML._

  val isRule = KLabel("isRule")

  def apply(m: Module): Module = {
    val newBody = pushDisjunction(m.rules map whatever(r => RewriteToTop.toLeft(r.body)))
    val newRequires = m.rules map whatever(_.requires) map { case (a, b) => and(a, b) } reduce { (a, b) => or(a, b) }
    Module(m.name, m.imports, m.localSentences + Rule(newBody, newRequires, True, Att()), m.att)
  }

  def whatever(relevant: Rule => K)(r: Rule): (K, K) = {
    (relevant(r), isRule(r.att.getK("Source").get, r.att.getK("Location").get))
  }

  def pushDisjunction(terms: Set[(K, K)]): K = {
    val disjunctionOfKApplies: Iterable[K] = terms
      .collect({ case (x: KApply, ruleP) => (x, ruleP) })
      .groupBy(_._1.klabel)
      .map { case (klabel: KLabel, ks: Set[(KApply, K)]) => {
        if (ks.size > 1) {
          val setOfLists: Set[List[(K, K)]] = ks map { case (kapply, ruleP) => kapply.klist.items.asScala.map((_, ruleP)).toList }
          val childrenDisjunctionsOfklabel: IndexedSeq[K] =
            setOfLists.head.indices
              .map(i => setOfLists.map(_ (i)))
              .map(pushDisjunction)

          klabel(childrenDisjunctionsOfklabel: _*)
        } else
          and(ks.head._1, ks.head._2)
      }
      }

    val disjunctionOfOthers: Set[K] = terms.filterNot(_._1.isInstanceOf[KApply]).map({ case (k, ruleP) => and(k, ruleP) })
    or((disjunctionOfKApplies ++ disjunctionOfOthers).toSeq: _*)
  }
}
