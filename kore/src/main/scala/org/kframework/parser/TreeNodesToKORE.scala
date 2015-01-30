package org.kframework.parser

import org.kframework.attributes._
import org.kframework.builtin.Sorts
import org.kframework.kore
import org.kframework.kore.{ADTConstructors => con, _}

import scala.collection.JavaConverters._

object TreeNodesToKORE {
  def apply(t: Term): K = t match {
    // TODO(Radu): the content of the constant should not be trimmed (see below) but we do this now due to an
    // but related to whitespace in the parser.
    case Constant(s, p, l) => con.KToken(p.sort, s.trim, locationToAtt(l.get()))
    case TermCons(items, p, l) => con.KApply(p.klabel, con.KList(items.asScala map apply asJava), locationToAtt(l.get()))
    case Ambiguity(items, l) => con.KApply(con.KLabel("AMB"), con.KList(items.asScala map apply asJava), Attributes())
  }

  def down(t: K): K = t match {
    // TODO(Radu): the content of the constant should not be trimmed (see below) but we do this now due to an
    // but related to whitespace in the parser.
    //    case Constant(s, p, l) if p.sort == Sorts.KLabel => KLabel(s.trim)
    case t@KToken(sort, s) if sort == Sorts.KVariable =>
      con.KVariable(s.trim, t.att)

    case t: kore.KToken => t
    case t@kore.KApply(KLabel("#KRewrite"), items: kore.KList) =>
      val it = items.items.iterator
      val res = con.KRewrite(down(it.next()), down(it.next()), t.att)
      assert(!it.hasNext)
      res

    case t@kore.KApply(KLabel("#KApply"), items) =>
      val theKList = items.tail.head match {
        case t@KApply(KLabel("#KList"), items) => con.KList((items map down _).asJava)
        case c: KToken => con.KList(down(c))
      }
      con.KApply(
        con.KLabel(items(0).asInstanceOf[KToken].s),
        theKList, t.att)

    case t@kore.KApply(KLabel("#KToken"), items) =>
      def removeQuotes(s: String) = s.drop(1).dropRight(1)

      con.KToken(con.Sort(removeQuotes(items(0).asInstanceOf[Constant].s)),
        removeQuotes(items.tail.head.asInstanceOf[Constant].s), t.att)

    case t@kore.KApply(l, items) => con.KApply(l, con.KList((items map down _).asJava), t.att)
  }

  def locationToAtt(l: Location): Attributes =
    Attributes(ObjectToKORE(Location(l.startLine, l.startColumn, l.endLine, l.endColumn)))
}
