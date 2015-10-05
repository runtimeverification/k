package org.kframework.compile

import org.kframework.Collections._
import org.kframework.builtin.KLabels
import org.kframework.kore.KORE._
import org.kframework.kore._


object CleanKSeq extends (K => K) {
  val self = this

  def apply(k: K): K = {
    k match {
      case kseq: KSequence =>
        val s: Seq[K] = Assoc.flatten(KLabel(KLabels.KSEQ), immutable(kseq.items), KLabel(KLabels.DOTK))
        val dotk = KLabels.DOTK
        s.last match {
          case Unapply.KApply(Unapply.KLabel(dotk), _) => kseq
          case kvar: KVariable => kseq
          case _ => s.foldLeft(KApply(KLabel(dotk)): K)((a, b) => KLabel(KLabels.KSEQ)(a, b))
        }
      case rw: KRewrite => KRewrite(apply(rw.left), apply(rw.right), rw.att)
      case app: KApply => KApply(app.klabel, immutable(app.klist.items) map apply, app.att)
      case other => other
    }
  }
}
