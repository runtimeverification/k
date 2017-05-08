package org.kframework.compile

import org.kframework.Collections._
import org.kframework.kore.KORE.{KApply, KAs, KSequence}
import org.kframework.kore.{KRewrite, _}


object RewriteToTop {
  def toLeft(rewrite: K): K = rewrite match {
    case t: KRewrite => t.left
    case t: KApply => KApply(t.klabel, immutable(t.klist.items) map toLeft, t.att)
    case t: KSequence => KSequence(mutable(immutable(t.items) map toLeft toList), t.att)
    case t: KAs => KAs(toLeft(t.pattern), t.alias)
    case other => other
  }

  def toRight(rewrite: K): K = rewrite match {
    case t: KRewrite => toRight(t.right) // recurse here because of KAs
    case t: KApply => KApply(t.klabel, immutable(t.klist.items) map toRight, t.att)
    case t: KSequence => KSequence(mutable(immutable(t.items) map toRight toList), t.att)
    case t: KAs => t.alias
    case other => other
  }


}
