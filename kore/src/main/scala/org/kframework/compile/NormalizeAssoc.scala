// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile

import org.kframework.attributes.Att
import org.kframework.definition.Module
import org.kframework.definition.Rule
import org.kframework.definition.Sentence
import org.kframework.kore._
import org.kframework.Collections._

/**
 * Compiler pass flattening associative collections
 */
class NormalizeAssoc(c: Constructors) extends ((Module, Sentence) => Sentence) {

  import c._

  def apply(m: Module, s: Sentence): Sentence = s match {
    case r: Rule =>
      Rule(apply(r.body)(m), apply(r.requires)(m), r.ensures, r.att)
    case _ => s
  }

  def apply(k: K)(implicit m: Module): K = k match {
    case kApply: KApply =>
      if (m.attributesFor.getOrElse(kApply.klabel, Att.empty).contains(Att.ASSOC)) {
        val opKLabel: KLabel   = kApply.klabel
        val unitKLabel: KLabel = KLabel(m.attributesFor(opKLabel).get(Att.UNIT))
        val flattenChildren    = flatten(kApply, opKLabel, unitKLabel)
        if (flattenChildren.exists(_.isInstanceOf[KRewrite])) {
          KRewrite(
            KApply(
              opKLabel,
              KList(flatten(RewriteToTop.toLeft(k), opKLabel, unitKLabel).map(apply)),
              kApply.att
            ),
            RewriteToTop.toRight(k),
            Att.empty
          )
        } else {
          KApply(opKLabel, KList(flattenChildren.map(apply)), kApply.att)
        }
      } else {
        KApply(kApply.klabel, KList(immutable(kApply.klist.items).map(apply)), kApply.att)
      }
    case kRewrite: KRewrite => KRewrite(apply(kRewrite.left), kRewrite.right, kRewrite.att)
    case _                  => k
  }

  def flatten(k: K, op: KLabel, unit: KLabel): Seq[K] = k match {
    case Unapply.KApply(`op`, children: List[K]) =>
      children.flatMap(flatten(_, op, unit))
    case Unapply.KApply(`unit`, List()) =>
      Seq()
    // case kRewrite: KRewrite =>
    // (flatten(kRewrite.left, op, unit) map {KRewrite(_, KApply(unit), kRewrite.att)}) :+
    // KRewrite(KApply(unit), kRewrite.right, kRewrite.att)
    case _ =>
      Seq(k)
  }

}
