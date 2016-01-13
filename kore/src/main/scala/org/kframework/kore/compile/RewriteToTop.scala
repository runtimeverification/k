package org.kframework.kore.compile

import org.kframework.kore.KORE.{KApply, KList, KSequence}
import org.kframework.kore.KRewrite
import org.kframework.kore._
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

  def bubbleRewriteOutOfKSeq(k: K): K = k match {
    case kseq: KSequence => ADT.KRewrite(toLeft(kseq), toRight(kseq))
    case t: KRewrite => ADT.KRewrite(t.left, t.right)
    case t: KApply => KApply(t.klabel, immutable(t.klist.items) map bubbleRewriteOutOfKSeq, t.att)
    case other => other
  }

  def bubbleRewriteToTopInsideCells(k: K): K = k match {
    case kapp: KApply =>
      if (isCell(kapp) && nonCell(kapp.items.get(0)))
        KApply(kapp.klabel, immutable(kapp.klist.items) map makeRewriteIfNeeded, kapp.att)
      else
        KApply(kapp.klabel, immutable(kapp.klist.items) map bubbleRewriteToTopInsideCells, kapp.att)
    case _ => k
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
