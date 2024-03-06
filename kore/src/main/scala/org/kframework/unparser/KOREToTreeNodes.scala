// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.unparser

import org.kframework.attributes.Att
import org.kframework.attributes.Location
import org.kframework.attributes.Source
import org.kframework.builtin.Sorts
import org.kframework.definition._
import org.kframework.kore._
import org.kframework.parser._
import org.kframework.POSet
import org.pcollections.ConsPStack
import scala.collection.{ IndexedSeq => _, Seq => _, _ }
import scala.collection.JavaConverters._

object KOREToTreeNodes {

  import org.kframework.kore.KORE._

  def wellTyped(
      args: immutable.Seq[Sort],
      p: Production,
      children: Iterable[Term],
      subsorts: POSet[Sort]
  ): Boolean = {
    val origP = p.att.getOptional(Att.ORIGINAL_PRD, classOf[Production]).orElse(p)
    val subst = origP.substitute(args)
    val rightPoly =
      (args.isEmpty && origP.params.nonEmpty) || (p.sort == subst.sort && p.items == subst.items)
    return rightPoly && p.nonterminals
      .zip(children)
      .forall(p =>
        !p._2.isInstanceOf[ProductionReference] || subsorts
          .lessThanEq(p._2.asInstanceOf[ProductionReference].production.sort, p._1.sort)
      )
  }

  def apply(t: K, mod: Module): Term = t match {
    case t: KToken =>
      Constant(
        t.s,
        mod.tokenProductionFor(t.sort),
        t.att.getOptional(Att.LOCATION, classOf[Location]),
        t.att.getOptional(Att.SOURCE, classOf[Source])
      )
    case a: KApply =>
      val scalaChildren = a.klist.items.asScala.map { i: K => apply(i, mod).asInstanceOf[Term] }
      val children      = ConsPStack.from(scalaChildren.reverse.asJava)
      val loc           = t.att.getOptional(Att.LOCATION, classOf[Location])
      val source        = t.att.getOptional(Att.SOURCE, classOf[Source])
      val p =
        mod.productionsFor(KLabel(a.klabel.name)).filter(!_.att.contains(Att.UNPARSE_AVOID)).head
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
        KORE.KApply(
          KORE.KLabel("#SemanticCastTo" + v.att.get(Att.SORT, classOf[org.kframework.kore.Sort])),
          KToken(v.name, Sorts.KVariable, v.att)
        )
      else
        KToken(v.name, Sorts.KVariable, v.att)
    case t: KToken =>
      val sort = Sort(t.sort.name, t.sort.params)
      KToken(t.s, sort, t.att)
    case s: KSequence =>
      upList(mod)(s.items.asScala.to[immutable.Seq])
        .foldRight(KApply(KLabel("#EmptyK"), KList(), s.att))((k1, k2) =>
          KApply(KLabel("#KSequence"), KList(k1, k2), s.att)
        )
    case r: KRewrite => KApply(KLabel("#KRewrite"), KList(up(mod)(r.left), up(mod)(r.right)), r.att)
    case t: KApply => KApply(t.klabel, upList(mod)(t.klist.items.asScala.to[immutable.Seq]), t.att)
  }

  def upList(mod: Module)(items: immutable.Seq[K]): immutable.Seq[K] =
    items.map(up(mod) _)
}
