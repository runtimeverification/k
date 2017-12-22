package org.kframework.compile

import org.kframework.Collections._
import org.kframework.builtin.KLabels
import org.kframework.kore.KORE._
import org.kframework.kore._

/**
  * Assumes KSequences are KApplys and puts them in right-assoc normal form
  */
object NormalizeKSeq extends (K => K) {
  val self = this

  val dotk = KLabel(KLabels.DOTK)
  val kseq = KLabel(KLabels.KSEQ)

  def apply(k: K): K = {
    k match {
      case app: KApply =>
        val convertedK: K = KApply(app.klabel, immutable(app.klist.items) map apply, app.att)
        if (app.klabel == kseq) normalize(convertedK) else convertedK
      case rw: KRewrite => KRewrite(apply(rw.left), apply(rw.right), rw.att)
      case other => other
    }
  }

  def normalize(k: K): K = {
    val s: Seq[K] = Assoc.flatten(kseq, Seq(k), dotk)
    (s.last match {
      case Unapply.KApply(`dotk`, _) => s
      case kvar: KVariable => s
      case _ => s :+ KApply(dotk)
    }).reduceRight((a, b) => kseq(a, b))
  }
}
