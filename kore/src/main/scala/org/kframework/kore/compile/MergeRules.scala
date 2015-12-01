package org.kframework.kore.compile

import org.kframework.attributes.Att
import org.kframework.builtin.KLabels
import org.kframework.definition.{Module, Rule}
import org.kframework.kore._

import scala.collection.JavaConverters._
import scala.collection.immutable.Iterable
import collection._

/**
 * Compiler pass for merging the rules as expected by FastRuleMatcher
 */
class MergeRules(c: Constructors[K]) extends (Module => Module) {

  import c._

  val s = new ScalaSugar(c)

  import s._

  object ML {
    val and = KLabel(KLabels.ML_AND)
    val or = KLabel(KLabels.ML_OR)
    val True = KLabel(KLabels.ML_TRUE)()
    val False = KLabel(KLabels.ML_FALSE)()
    val TrueToken: K = KToken("true", Sort("Bool"), Att())
  }

  import ML._

  val isRulePredicate = KLabel("isRule")

  def apply(m: Module): Module = {
    val topRules = m.rules filter {_.att.contains(Att.topRule)}

    if (topRules.nonEmpty) {

      val newBody = pushDisjunction(topRules map { r => (convertKRewriteToKApply(r.body), isRulePredicate(r.hashCode)) })
      //      val newRequires = makeOr((topRules map whatever(_.requires) map { case (a, b) => and(a, b) }).toSeq: _*)
      //val automatonRule = Rule(newBody, newRequires, TrueToken, Att().add("automaton"))
      val automatonRule = Rule(newBody, TrueToken, TrueToken, Att().add("automaton"))
      Module(m.name, m.imports, m.localSentences + automatonRule, m.att)
    } else {
      m
    }
  }

  def convertKRewriteToKApply(k: K): K = k match {
    case Unapply.KApply(label, children) => label(children map convertKRewriteToKApply: _*)
    case Unapply.KRewrite(l, r) => KLabel(KLabels.KREWRITE)(l, r)
    case other => other
  }

  def makeOr(ks: K*): K = {
    if (ks.size == 1) {
      ks.head
    } else {
      or(ks: _*)
    }
  }


  def pushDisjunction(terms: Set[(K, K)]): K = {
    val rwLabel = KLabel(KLabels.KREWRITE)

    val removedRewrites = terms.map({
      case (Unapply.KApply(`rwLabel`, children), ruleP) => (children.head, ruleP)
      case other => other
    })

    val normalizedTerms: Set[(K, K)] = removedRewrites map { p => (normalizeKSeq(p._1), p._2) }

    val theRewrites = terms
      .collect { case (Unapply.KApply(`rwLabel`, children), ruleP) => (children.last, ruleP) }
      .map { p => (normalizeKSeq(p._1), p._2) }

    val disjunctionOfKApplies: Iterable[(K, K)] = normalizedTerms
      .collect({ case (x: KApply, ruleP) => (x, ruleP) })
      .groupBy(_._1.klabel)
      .map {
        case (klabel: KLabel, ks: Set[(KApply, K)]) =>
          val setOfLists: Set[List[(K, K)]] = ks map { case (kapply, ruleP) => kapply.klist.items.asScala.map((_, ruleP)).toList }
          val childrenDisjunctionsOfklabel: IndexedSeq[K] =
            setOfLists.head.indices
              .map(i => setOfLists.map(l => l(i)))
              .map(pushDisjunction)
          val rulePs = ks map {_._2} toSeq

          (klabel(childrenDisjunctionsOfklabel: _*), or(rulePs: _*))
      }

    val disjunctionOfOthers: Iterable[(K, K)] = normalizedTerms.filterNot(_._1.isInstanceOf[KApply])
      .groupBy(_._1)
      .map({ case (k, set) => (k, set.map(_._2)) })
      .map({ case (k, rulePs) => (k, makeOr(rulePs.toSeq: _*)) })

    val entireDisjunction: Iterable[(K, K)] = disjunctionOfKApplies ++ disjunctionOfOthers
    val theLHS = if (entireDisjunction.size == 1)
      entireDisjunction.head._1
    else
      makeOr(entireDisjunction.map({ case (a, b) => and(a, b) }).toSeq: _*)

    if (theRewrites.nonEmpty) {
      rwLabel(theLHS, makeOr(theRewrites.map({ case (a, b) => and(a, b) }).toSeq: _*))
    } else {
      theLHS
    }
  }

  def normalizeKSeq(k: K): K = Assoc.flatten(KLabel(KLabels.KSEQ), Seq(k), KLabel(KLabels.DOTK)) reduceRightOption { (a, b) => KLabel(KLabels.KSEQ)(a, b) } getOrElse {KLabel(KLabels.DOTK)()}
}
