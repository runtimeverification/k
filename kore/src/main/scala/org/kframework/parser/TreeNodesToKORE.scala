package org.kframework.parser

import org.kframework.attributes._
import org.kframework.builtin.Sorts
import org.kframework.kore
import org.kframework.kore.Unapply._
import org.kframework.kore.{ADTConstructors => con, _}

import scala.collection.JavaConverters._

object TreeNodesToKORE {

  import con._

  def apply(t: Term): K = t match {
    // TODO(Radu): the content of the constant should not be trimmed (see below) but we do this now due to an
    // but related to whitespace in the parser.
    case Constant(s, p, l) => KToken(p.sort, s.trim, locationToAtt(l.get()))
    case TermCons(items, p, l) => KApply(p.klabel.get, KList(items.asScala map apply asJava), locationToAtt(l.get()))
    case Ambiguity(items, l) => KApply(KLabel("AMB"), KList(items.asScala.toList map apply asJava), Att())
  }

  def down(t: K): K = t match {
    // TODO(Radu): the content of the constant should not be trimmed (see below) but we do this now due to an
    // but related to whitespace in the parser.
    //    case Constant(s, p, l) if p.sort == Sorts.KLabel => KLabel(s.trim)
    case t@KToken(sort, s) if sort == Sorts.KVariable =>
      KVariable(s.trim, t.att)

    case t: kore.KToken => t
    case t@KApply(KLabel("#KRewrite"), items: kore.KList) =>
      val it = items.items.iterator
      val res = KRewrite(down(it.next()), down(it.next()), t.att)
      assert(!it.hasNext)
      res

    case t@KApply(KLabel("#KApply"), items) =>
      val theKList = items.tail.head match {
        case t@KApply(KLabel("#KList"), items) => KList((items map down _).asJava)
        case c: KToken => KList(down(c))
      }
      KApply(
        KLabel(items(0).asInstanceOf[KToken].s),
        theKList, t.att)

    case t@KApply(KLabel("#KToken"), items) =>
      def removeQuotes(s: String) = s.drop(1).dropRight(1)

      KToken(Sort(removeQuotes(items(0).asInstanceOf[Constant].s)),
        removeQuotes(items.tail.head.asInstanceOf[Constant].s), t.att)

    case t@KApply(l, items) => KApply(l, KList((items map down _).asJava), t.att)
  }

  def locationToAtt(l: Location): Att =
    Att(ObjectToKORE(Location(l.startLine, l.startColumn, l.endLine, l.endColumn)))
}
