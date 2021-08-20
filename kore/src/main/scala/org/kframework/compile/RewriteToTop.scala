package org.kframework.compile

import org.kframework.Collections._
import org.kframework.kore.KORE.{KApply, KAs, KSequence, KLabel}
import org.kframework.kore.{KRewrite, _}
import org.kframework.utils.errorsystem.KEMException;


object RewriteToTop {
  def toLeft(rewrite: K): K = rewrite match {
    case t: KRewrite => t.left
    case t: KApply => compactInjections(KApply(t.klabel, t.klist.scalaItems map toLeft, t.att))
    case t: KSequence => KSequence(mutable(t.scalaItems map toLeft toList), t.att)
    case t: KAs => KAs(toLeft(t.pattern), t.alias, t.att)
    case other => other
  }

  def toRight(rewrite: K): K = rewrite match {
    case t: KRewrite => toRight(t.right) // recurse here because of KAs
    case t: KApply => compactInjections(KApply(t.klabel, t.klist.scalaItems map toRight, t.att))
    case t: KSequence => KSequence(mutable(t.scalaItems map toRight toList), t.att)
    case t: KAs => t.alias
    case other => other
  }


  def bubbleRewriteToTopInsideCells(k: K): K = k match {
    case kapp: KApply =>
      if (isCell(kapp) && nonCell(kapp.items.get(0)))
        KApply(kapp.klabel, kapp.klist.scalaItems map makeRewriteIfNeeded, kapp.att)
      else
        KApply(kapp.klabel, kapp.klist.scalaItems map bubbleRewriteToTopInsideCells, kapp.att)
    case _ => k
  }


  def nonCell(k: K): Boolean = k match {
    case kapp: KApply => if (!isCell(kapp)) {
      kapp.klist.scalaItems map nonCell forall { b => b }
    } else {
      false
    }
    case rw: KRewrite => nonCell(rw.left) && nonCell(rw.right)
    case _ => true
  }

  def hasRewrite(k: K): Boolean = k match {
    case t: KRewrite => true
    case t: KApply => t.klist.scalaItems.foldLeft(false)((b,k) => b || hasRewrite(k))
    case t: KSequence => t.scalaItems.foldLeft(false)((b,k) => b || hasRewrite(k))
    case other => false
  }

  private def isCell(kapp: KApply): Boolean = {
    kapp.klabel.name.startsWith("<") && kapp.klabel.name.endsWith(">")
  }

  private def makeRewriteIfNeeded(k: K): K = if (toLeft(k) != toRight(k)) ADT.KRewrite(toLeft(k), toRight(k)) else k

  private def compactInjections(k: K): K = k match {
    case kapp: KApply =>
      val args: Seq[K] = kapp.klist.scalaItems
      if (isInjection(kapp) && args.length == 1 && isInjection(args.head)) {
        val kappInner: KApply = args.head.asInstanceOf[KApply]
        val sortsOuter: List[Sort] = kapp.klabel.params.toList
        val sortsInner: List[Sort] = kappInner.klabel.params.toList
        if (sortsOuter.length != 2 || sortsInner.length != 2) {
          throw KEMException.internalError(
                  "Injection compaction error: found injection with more than two sort parameters")
        }
        val sortOuterIn:  Sort = sortsOuter.head
        val sortOuterOut: Sort = sortsOuter.last
        val sortInnerIn:  Sort = sortsInner.head
        val sortInnerOut: Sort = sortsInner.last
        if (sortInnerOut != sortOuterIn) {
          throw KEMException.internalError(
                  "Injection compaction error: found nested injections with incompatible sorts")
        }
        KApply(KLabel("inj", List(sortInnerIn, sortOuterOut): _*), kappInner.klist, kapp.att)
      } else {
        kapp
      }
    case other => other
  }

  private def isInjection(k: K): Boolean = k match {
    case kapp: KApply => kapp.klabel.name == "inj"
    case other => false
  }

}
