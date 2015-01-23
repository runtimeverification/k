package org.kframework.parser

import org.kframework._
import org.kframework.kore._
import outer._
import collection.JavaConverters._
import org.kframework.builtin.Sorts

object TreeNodesToKORE {
  def apply(t: Term): K = t match {
    // TODO(Radu): the content of the constant should not be trimmed (see below) but we do this now due to an
    // but related to whitespace in the parser.
    case Constant(s, p, l) => KToken(p.sort, s.trim, locationToAtt(l.get()))
    case TermCons(items, p, l) => KApply(p.klabel.get, kore.KList(items.asScala map apply), locationToAtt(l.get()))
    case Ambiguity(items, l) => KApply(KLabel("AMB"), kore.KList(items.asScala map apply), Attributes())
  }

  def down(t: K): K = t match {
    // TODO(Radu): the content of the constant should not be trimmed (see below) but we do this now due to an
    // but related to whitespace in the parser.
    //    case Constant(s, p, l) if p.sort == Sorts.KLabel => KLabel(s.trim)
    case KToken(sort, s, att) if sort == Sorts.KVariable =>
      KVariable(s.trim, att)

    case t: KToken => t
    case KApply(KLabel("#KRewrite"), items, att) =>
      KRewrite(items map down _, att)

    case KApply(KLabel("#KApply"), items, att) =>
      val theKList = items.tail.head match {
        case KApply(KLabel("#KList"), items, att) => items map down _
        case c: KToken => kore.KList(down(c))
      }
      KApply(
        KLabel(items(0).asInstanceOf[KToken].s),
        theKList, att)

    case KApply(KLabel("#KToken"), items, att) =>
      def removeQuotes(s: String) = s.drop(1).dropRight(1)

      KToken(Sort(removeQuotes(items(0).asInstanceOf[Constant].s)),
        removeQuotes(items.tail.head.asInstanceOf[Constant].s))

    case KApply(l, items, att) => KApply(l, items map down _, att)
  }

  def locationToAtt(l: org.kframework.parser.Location): Attributes =
    Attributes(tiny.builtin.Location.apply(l.startLine, l.startColumn, l.endLine, l.endColumn))
}
