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
    if (!m.rules.isEmpty) {
      val topRules = m.rules filter { r => r.body match {
        case app: KApply => app.klabel.name == "<T>"
        case _ => false
      }
      }

      val newBody = pushDisjunction(topRules map whatever(r => RewriteToTop.toLeft(r.body)))
      val newRequires = or((topRules map whatever(_.requires) map { case (a, b) => and(a, b) }).toSeq: _*)
      Module(m.name, m.imports, m.localSentences + Rule(newBody, newRequires, True, Att()), m.att)
    } else {
      m
    }
  }

  def whatever(relevant: Rule => K)(r: Rule): (K, K) = {
    (relevant(r), isRule(r.hashCode))
  }

  def or(ks: K*): K = {
    if (ks.size == 1) {
      ks.head
    } else {
      ML.or(ks: _*)
    }
  }

  def pushDisjunction(terms: Set[(K, K)]): K = {
    val disjunctionOfKApplies: Iterable[(K, K)] = terms
      .collect({ case (x: KApply, ruleP) => (x, ruleP) })
      .groupBy(_._1.klabel)
      .map { case (klabel: KLabel, ks: Set[(KApply, K)]) => {
        if (ks.size > 1) {
          val setOfLists: Set[List[(K, K)]] = ks map { case (kapply, ruleP) => kapply.klist.items.asScala.map((_, ruleP)).toList }
          val childrenDisjunctionsOfklabel: IndexedSeq[K] =
            setOfLists.head.indices
              .map(i => setOfLists.map(_ (i)))
              .map(pushDisjunction)
          val rulePs = ks map { _._2 } toSeq

          (klabel(childrenDisjunctionsOfklabel: _*), or(rulePs: _*))
        } else
          (ks.head._1, ks.head._2)
      }
      }

    val disjunctionOfOthers: Iterable[(K, K)] = terms.filterNot(_._1.isInstanceOf[KApply])
      .groupBy(_._1)
      .map({ case (k, set) => (k, set.map(_._2)) })
      .map({ case (k, rulePs) => (k, or(rulePs.toSeq: _*)) })

    val entireDisjunction = disjunctionOfKApplies ++ disjunctionOfOthers
    if (entireDisjunction.size == 1)
      entireDisjunction.head._1
    else
      or(entireDisjunction.map({ case (a, b) => and(a, b) }).toSeq: _*)
  }
}
