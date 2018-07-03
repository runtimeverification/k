package org.kframework.unparser

import org.kframework.attributes.{Location, Source}
import org.kframework.builtin.Sorts
import org.kframework.definition._
import org.kframework.kore.{KApply, KToken, KVariable, _}
import org.kframework.parser.{Constant, ProductionReference, Term, TermCons}
import org.pcollections.ConsPStack

import collection._
import JavaConverters._

object KOREToTreeNodes {

  import org.kframework.kore.KORE._

  def apply(t: K, mod: Module): ProductionReference = t match {
    case t: KToken => Constant(t.s, mod.tokenProductionsFor(t.sort).head, t.att.getOptional(classOf[Location]), t.att.getOptional(classOf[Source]))
    case a: KApply =>
      val production: Production = mod.productionsFor(KLabel(a.klabel.name)).find(p => p.items.count(_.isInstanceOf[NonTerminal]) == a.klist.size && !p.att.contains("unparseAvoid")).get
      TermCons(ConsPStack.from((a.klist.items.asScala map { i: K => apply(i, mod).asInstanceOf[Term] }).reverse asJava),
        production, t.att.getOptional(classOf[Location]), t.att.getOptional(classOf[Source]))
  }

  def up(mod: Module)(t: K): K = t match {
    case v: KVariable => KToken(v.toString, Sorts.KVariable, v.att)
    case t: KToken =>
      if (mod.tokenProductionsFor.contains(t.sort)) {
        t
      } else {
        KToken(t.s, Sorts.KString, t.att)
      }
    case s: KSequence =>
      if (s.items.size() == 0)
        KApply(KLabel("#EmptyK"), KList(), s.att)
      else
        upList(mod)(s.items.asScala).reduce((k1, k2) => KApply(KLabel("#KSequence"), KList(k1, k2), s.att))
    case r: KRewrite => KApply(KLabel("#KRewrite"), KList(up(mod)(r.left), up(mod)(r.right)), r.att)
    case t: KApply => KApply(t.klabel, upList(mod)(t.klist.items.asScala), t.att)
  }

  def upList(mod: Module)(items: Seq[K]): Seq[K] = {
    items map up(mod) _
  }
}
