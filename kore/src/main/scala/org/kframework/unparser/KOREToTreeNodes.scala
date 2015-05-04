package org.kframework.unparser

import org.kframework.attributes.{Location, Source}
import org.kframework.builtin.Sorts
import org.kframework.definition.{Module, NonTerminal, Terminal}
import org.kframework.kore.{KApply, KToken, KVariable, _}
import org.kframework.parser.{Constant, Term, TermCons}
import org.pcollections.ConsPStack

import scala.collection.JavaConverters._

object KOREToTreeNodes {

  import org.kframework.kore.KORE._

  def apply(t: K, mod: Module): Term = t match {
    case t: KToken => Constant(t.s, mod.tokenProductionsFor(Sort(t.sort.name)).head, t.att.getOptional[Location]("Location"), t.att.getOptional[Source]("Source"))
    case a: KApply => TermCons(ConsPStack.from((a.klist.items.asScala map { i:K => apply(i, mod) }).reverse asJava),
      mod.productionsFor(KLabel(a.klabel.name)).head, t.att.getOptional[Location]("Location"), t.att.getOptional[Source]("Source"))
  }

  def up(t: K): K = t match {
    case v: KVariable => KToken(Sorts.KVariable, v.name, v.att)
    case t: KToken => t
    case s: KSequence =>
      if (s.items.size() == 0)
        KApply(KLabel("#EmptyK"), KList(), s.att)
      else
        KApply(KLabel("#KSequence"), upList(s.items.asScala), s.att)
    case r: KRewrite => KApply(KLabel("#KRewrite"), KList(up(r.left), up(r.right)), r.att)
    case t: KApply => KApply(t.klabel, upList(t.klist.items.asScala), t.att)
  }

  def upList(items: Seq[K]): Seq[K] = {
    items map up _
  }

  def toString(t: Term): String = t match {
    case Constant(s, _) => s
    case t@TermCons(items, p) => {
      var i = 0
      val unparsedItems = p.items map {
        case Terminal(s, _) => s
        case NonTerminal(sort) => {
          i = i + 1
          toString(t.get(i - 1))
        }
      }
      if (p.att.contains("format")) {
        p.att.get[String]("format").get.format(unparsedItems:_*)
      } else {
        unparsedItems.mkString(" ")
      }
    }
  }
}
