package org.kframework.kore.compile

import org.kframework.kore.KORE.{KApply, KList, KAs, KSequence}
import org.kframework.kore.KRewrite
import org.kframework.kore._
import org.kframework.Collections._


object RewriteToTop {
  def toLeft(rewrite: K): K = rewrite match {
    case t: KRewrite => t.left
    case t: KApply => KApply(t.klabel, immutable(t.klist.items) map toLeft, t.att)
    case t: KSequence => KSequence(mutable(immutable(t.items) map toLeft toList), t.att)
    case t: KAs => KAs(toLeft(t.pattern), t.alias)
    case other => other
  }

  def toRight(rewrite: K): K = rewrite match {
    case t: KRewrite => t.right
    case t: KApply => KApply(t.klabel, immutable(t.klist.items) map toRight, t.att)
    case t: KSequence => KSequence(mutable(immutable(t.items) map toRight toList), t.att)
    case t: KAs => t.alias
    case other => other
  }


  def nonCell(k: K): Boolean = k match {
    case kapp: KApply => if (!isCell(kapp)) {
      immutable(kapp.klist.items) map nonCell forall { b => b }
    } else {
      false
    }
    case rw: KRewrite => nonCell(rw.left) && nonCell(rw.right)
    case _ => true
  }

  private def isCell(kapp: KApply): Boolean = {
    kapp.klabel.name.startsWith("<") && kapp.klabel.name.endsWith(">")
  }

  private def makeRewriteIfNeeded(k: K): K = if (toLeft(k) != toRight(k)) ADT.KRewrite(toLeft(k), toRight(k)) else k

}
