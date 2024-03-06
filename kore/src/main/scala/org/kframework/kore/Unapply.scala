// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kore

import collection.JavaConverters._
import org.kframework.kore
import scala.collection.immutable

/**
 * Scala deconstructors for inner KORE objects.
 */

object Unapply {

  // objects for unapply -- we keep them in the same file as Scala requires this

  object KLabel {
    def unapply(klabel: KLabel) = Some(klabel.name)
  }

  object KToken {
    def unapply(token: KToken) = Some(token.s, token.sort)
  }

  object InjectedKLabel {
    def unapply(l: InjectedKLabel): Option[KLabel] = Some(l.klabel)
  }

  object Sort {
    def unapply(sort: Sort) = Some(sort.name, sort.params)
  }

  object KApply {
    def unapply(kapply: KApply) = Some(kapply.klabel, kapply.klist.items.asScala.toList)
  }

  object KSequence {
    def unapply(kseq: KSequence): Option[immutable.Seq[K]] = Some(
      kseq.items.asScala.to[immutable.Seq]
    )
  }

  object KRewrite {
    def unapply(krw: KRewrite): Option[(K, K)] = Some(krw.left, krw.right)
  }

  object KAs {
    def unapply(krw: KAs): Option[(K, K)] = Some(krw.pattern, krw.alias)
  }

  object KVariable {
    def unapply(v: KVariable): Option[String] = Some(v.name)
  }

  object KList {

    import scala.collection.JavaConverters._

    def unapplySeq(klist: KList): Option[immutable.Seq[kore.K]] = Some(
      klist.items.asScala.to[immutable.Seq]
    )
  }

}
