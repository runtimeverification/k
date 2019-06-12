package org.kframework.compile

import org.kframework.attributes.Att
import org.kframework.builtin.{KLabels, Sorts}
import org.kframework.definition.{Module, ModuleTransformer, Rule}
import org.kframework.kore._
import org.kframework.kore.KORE.{KApply, KLabel, KToken, Sort}
import org.kframework.kore.{K, KApply, KLabel, KVariable, Unapply, Assoc}

import scala.collection.JavaConverters._
import scala.collection.immutable.Iterable
import collection._

/**
  * Compiler pass for merging the rules as expected by FastRuleMatcher
  */
class MergeRules(val automatonAttribute: String, filterAttribute: String) extends Function[Module, Module] {


  object ML {
    val and = KLabels.ML_AND
    val or = KLabels.ML_OR
    val True = KApply(KLabels.ML_TRUE)
    val False = KApply(KLabels.ML_FALSE)
    val TrueToken: K = KToken("true", Sorts.Bool, Att.empty)
  }

  import ML._

  val isRulePredicate = KLabel("isRule")

  def apply(m: Module): Module = {
    val rulesToMerge = m.rules filter {_.att.contains(filterAttribute)}

    if (rulesToMerge.nonEmpty) {
      val newBody = pushDisjunction(rulesToMerge map { r => (convertKRewriteToKApply(r.body), KApply(isRulePredicate,KToken(r.hashCode.toString, Sorts.K, Att.empty))) })(m)
      val automatonRule = Rule(newBody, TrueToken, TrueToken, Att.empty.add(automatonAttribute))
      Module(m.name, m.imports, m.localSentences + automatonRule, m.att)
    } else {
      m
    }
  }

  private def convertKRewriteToKApply(k: K): K = k match {
    case Unapply.KApply(label, children) => KApply(label, (children map convertKRewriteToKApply: _*))
    case Unapply.KRewrite(l, r) => KApply(KLabels.KREWRITE,l, r)
    case other => other
  }

  private def makeOr(ks: K*): K = {
    if (ks.size == 1) {
      ks.head
    } else {
      KApply(or,ks: _*)
    }
  }

  private def pushDisjunction(terms: Set[(K, K)])(implicit m: Module): K = {
    val rwLabel = KLabels.KREWRITE

    val termsWithoutRewrites: Set[(K, K)] = terms.map({
      case (Unapply.KApply(`rwLabel`, children), ruleP) => (children.head, ruleP)
      case other => other
    })

    val theRewrites: Set[(K, K)] = terms collect { case (Unapply.KApply(`rwLabel`, children), ruleP) => (children.last, ruleP) }

    val disjunctionOfKApplies: Iterable[(K, K)] = termsWithoutRewrites
      .collect({ case (x: KApply, ruleP) if !x.klabel.isInstanceOf[KVariable] => (x, ruleP) })
      .groupBy(_._1.klabel)
      .map {
        case (klabel: KLabel, ks: Set[(KApply, K)]) =>
          val klistPredicatePairs: Set[(Seq[K], K)] = ks map { case (kapply, ruleP) => (kapply.klist.items.asScala.toSeq, ruleP) }
          val normalizedItemsPredicatePairs = if (isEffectiveAssoc(klabel, m) || klabel == KLabels.KSEQ) {
            val unitKLabel: KLabel = if (klabel != KLabels.KSEQ) KLabel(m.attributesFor(klabel).get(Att.unit)) else KLabels.DOTK
            val unitK: K = KApply(unitKLabel)
            val flatItemsPredicatePairs: Set[(Seq[K], K)] = klistPredicatePairs map { case (items, ruleP) => (Assoc.flatten(klabel, items, unitKLabel), ruleP) }
            val maxLength: Int = (flatItemsPredicatePairs map { _._1.size }).max
            flatItemsPredicatePairs map {  case (items, ruleP) =>  (items.padTo(maxLength, unitK), ruleP) }
          } else {
            klistPredicatePairs
          }
          val setOfLists: Set[Seq[(K, K)]] = normalizedItemsPredicatePairs map { case (items, ruleP) => items.map((_, ruleP)) }
          val childrenDisjunctionsOfklabel: IndexedSeq[K] =
            setOfLists.head.indices
              .map(i => setOfLists.map(l => l(i)))
              .map(pushDisjunction)
          val rulePs = ks map {_._2} toSeq

          (KApply(klabel,childrenDisjunctionsOfklabel: _*), KApply(or,rulePs: _*))
      }

    val disjunctionOfVarKApplies: Iterable[(K, K)] = termsWithoutRewrites
      .collect({ case (x: KApply, ruleP: K) if x.klabel.isInstanceOf[KVariable] => (x, ruleP) })
      .toIndexedSeq

    val disjunctionOfOthers: Iterable[(K, K)] = termsWithoutRewrites.filterNot(_._1.isInstanceOf[KApply])
      .groupBy(_._1)
      .map({ case (k, set) => (k, set.map(_._2)) })
      .map({ case (k, rulePs) => (k, makeOr(rulePs.toSeq: _*)) })

    val entireDisjunction: Iterable[(K, K)] = disjunctionOfKApplies ++ disjunctionOfVarKApplies ++ disjunctionOfOthers
    val theLHS = if (entireDisjunction.size == 1)
      entireDisjunction.head._1
    else
      makeOr(entireDisjunction.map({ case (a, b) => KApply(and,a, b) }).toSeq: _*)

    if (theRewrites.nonEmpty) {
      KApply(rwLabel,theLHS, makeOr(theRewrites.map({ case (a, b) => KApply(and,a, b) }).toSeq: _*))
    } else {
      theLHS
    }
  }

  private def isEffectiveAssoc(kLabel: KLabel, module: Module) : Boolean = {
    module.attributesFor.getOrElse(kLabel, Att.empty).contains(Att.assoc) && (!module.attributesFor.getOrElse(kLabel, Att.empty).contains(Att.comm)) || module.attributesFor.getOrElse(kLabel, Att.empty).contains(Att.bag)
  }

}
