package org.kframework.kore

import org.kframework.kore
import collection.JavaConverters._

/**
 * Scala deconstructors for inner KORE objects.
 */

object Unapply {

  // objects for unapply -- we keep them in the same file as Scala requires this

  object KLabel {
    def unapply(klabel: KLabel) = Some(klabel.name)
  }

  object KToken {
    def unapply(token: KToken) = Some(token.sort, token.s)
  }

  object Sort {
    def unapply(sort: Sort) = Some(sort.name)
  }

  object KApply {
    def unapply(kapply: KApply) = Some(kapply.klabel, kapply.klist.items.asScala.toList)
  }

  object KSequence {
    def unapply(kseq: KSequence): Option[Seq[K]] = Some(kseq.items.asScala.toSeq)
  }

  object KRewrite {
    def unapply(krw: KRewrite): Option[(K, K)] = Some(krw.left, krw.right)
  }

  object KVariable {
    def unapply(v: KVariable): Option[String] = Some(v.name)
  }

  object KList {

    import scala.collection.JavaConverters._

    def unapplySeq(klist: KList): Option[Seq[kore.K]] = Some(klist.items.asScala.toSeq)
  }

}
