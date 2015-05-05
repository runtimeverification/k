package org.kframework.kore.compile

import org.kframework.kore.KORE.{KApply, KList, KSequence}
import org.kframework.kore.{KSequence, K, KApply, KRewrite}
import org.kframework.Collections._


object RewriteToTop {
  def toLeft(rewrite: K): K = rewrite match {
    case t: KRewrite => t.left
    case t: KApply => KApply(t.klabel, immutable(t.klist.items) map toLeft, t.att)
    case t: KSequence => KSequence(mutable(immutable(t.items) map toLeft toList), t.att)
    case other => other
  }

  def toRight(rewrite: K): K = rewrite match {
    case t: KRewrite => t.right
    case t: KApply => KApply(t.klabel, immutable(t.klist.items) map toRight, t.att)
    case t: KSequence => KSequence(mutable(immutable(t.items) map toRight toList), t.att)
    case other => other
  }
}
