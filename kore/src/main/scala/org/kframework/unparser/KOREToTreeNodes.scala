package org.kframework.unparser

import java.util

import org.kframework.POSet
import org.kframework.attributes.{Location, Source}
import org.kframework.builtin.Sorts
import org.kframework.definition._
import org.kframework.kore.{KApply, KToken, KVariable, _}
import org.kframework.parser.{KList => _, _}
import org.pcollections.ConsPStack

import collection._
import JavaConverters._

object KOREToTreeNodes {

  import org.kframework.kore.KORE._

  def wellTyped(p: Production, children: ConsPStack[Term], subsorts: POSet[Sort]): Boolean = {
    if (p.nonterminals.lengthCompare(children.size()) != 0)
      return false
    true
  }

  def apply(t: K, mod: Module): Term = t match {
    case t: KToken => Constant(t.s, mod.tokenProductionFor(t.sort), t.att.getOptional(classOf[Location]), t.att.getOptional(classOf[Source]))
    case a: KApply =>
      val children = ConsPStack.from((a.klist.items.asScala map { i: K => apply(i, mod).asInstanceOf[Term] }).reverse asJava)
      val productions: Set[Production] = mod.productionsFor(KLabel(a.klabel.name)).filter(p => wellTyped(p, children, mod.subsorts) && !p.att.contains("unparseAvoid"))
      val loc = t.att.getOptional(classOf[Location])
      val source = t.att.getOptional(classOf[Source])
      if (productions.size == 1) {
        TermCons(children, productions.head, loc, source)
      } else {
        Ambiguity(new util.HashSet(productions.map(p => TermCons(children, p, loc, source).asInstanceOf[Term]).asJava))
      }
  }

  def up(mod: Module)(t: K): K = t match {
    case v: KVariable => KToken(v.toString, Sorts.KVariable, v.att)
    case t: KToken =>
      val sort = Sort(t.sort.name, t.sort.params:_*)
      KToken(t.s, sort, t.att)
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
