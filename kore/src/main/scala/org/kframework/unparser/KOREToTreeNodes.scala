// Copyright (c) K Team. All Rights Reserved.
package org.kframework.unparser

import java.util

import org.kframework.POSet
import org.kframework.attributes.{Att, Location, Source}
import org.kframework.builtin.Sorts
import org.kframework.definition._
import org.kframework.kore.{KApply, KToken, KVariable, _}
import org.kframework.parser._
import org.kframework.utils.StringUtil
import org.pcollections.ConsPStack

import collection._
import JavaConverters._

object KOREToTreeNodes {

  import org.kframework.kore.KORE.{Att => _, _}

  def wellTyped(args: Seq[Sort], p: Production, children: Iterable[Term], subsorts: POSet[Sort]): Boolean = {
    val origP = p.att.getOptional(Att.ORIGINAL_PRD, classOf[Production]).orElse(p)
    val subst = origP.substitute(args)
    val rightPoly = (args.isEmpty && origP.params.nonEmpty) || (p.sort == subst.sort && p.items == subst.items)
    return rightPoly && p.nonterminals.zip(children).forall(p => !p._2.isInstanceOf[ProductionReference] || subsorts.lessThanEq(p._2.asInstanceOf[ProductionReference].production.sort, p._1.sort))
  }

  def apply(t: K, mod: Module): Term = t match {
    case t: KToken => Constant(t.s, mod.tokenProductionFor(t.sort), t.att.getOptional(classOf[Location]), t.att.getOptional(classOf[Source]))
    case a: KApply =>
      val scalaChildren = a.klist.items.asScala map { i: K => apply(i, mod).asInstanceOf[Term] }
      val children = ConsPStack.from(scalaChildren.reverse asJava)
      val loc = t.att.getOptional(classOf[Location])
      val source = t.att.getOptional(classOf[Source])
      val p = mod.productionsFor(KLabel(a.klabel.name)).filter(!_.att.contains(Att.UNPARSE_AVOID)).head
      val subst = if (a.klabel.params.nonEmpty) {
        val origP = p.att.getOptional(Att.ORIGINAL_PRD, classOf[Production]).orElse(p)
        origP.substitute(a.klabel.params)
      } else {
        p
      }
      TermCons(children, subst, loc, source)
  }

  def up(mod: Module)(t: K): K = t match {
    case v: KVariable =>
      if (v.att.contains(Att.PRETTY_PRINT_WITH_SORT_ANNOTATION))
        KORE.KApply(KORE.KLabel("#SemanticCastTo" + v.att.get(classOf[org.kframework.kore.Sort])), KToken(v.name, Sorts.KVariable, v.att))
      else
        KToken(v.name, Sorts.KVariable, v.att)
    case t: KToken =>
      val sort = Sort(t.sort.name, t.sort.params:_*)
      KToken(t.s, sort, t.att)
    case s: KSequence =>
      upList(mod)(s.items.asScala).foldRight(KApply(KLabel("#EmptyK"), KList(), s.att))((k1, k2) => KApply(KLabel("#KSequence"), KList(k1, k2), s.att))
    case r: KRewrite => KApply(KLabel("#KRewrite"), KList(up(mod)(r.left), up(mod)(r.right)), r.att)
    case t: KApply => KApply(t.klabel, upList(mod)(t.klist.items.asScala), t.att)
  }

  def upList(mod: Module)(items: Seq[K]): Seq[K] = {
    items map up(mod) _
  }
}
