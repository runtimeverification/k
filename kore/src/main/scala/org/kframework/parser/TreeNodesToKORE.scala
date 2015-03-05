package org.kframework.parser

import org.kframework.attributes._
import org.kframework.builtin.Sorts
import org.kframework.kore
import org.kframework.kore.Unapply._
import org.kframework.kore.{Constructors => con, _}
import org.kframework.meta.Up

import scala.collection.JavaConverters._

object TreeNodesToKORE {

  import org.kframework.kore.KORE._

  def apply(t: Term): K = t match {
    case Constant(s, p, l) => KToken(p.sort, s, locationToAtt(l.get()))
    case TermCons(items, p, l) => KApply(p.klabel.get, KList(items.asScala map apply asJava), locationToAtt(l.get()))
    case Ambiguity(items, l) => KApply(KLabel("AMB"), KList(items.asScala.toList map apply asJava), Att())
  }

  def down(t: K): K = t match {
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

      KToken(Sort(removeQuotes(items(0).asInstanceOf[Constant].value)),
        removeQuotes(items.tail.head.asInstanceOf[Constant].value))

    case t@KApply(l, items) => KApply(l, KList((items map down _).asJava), t.att)
  }

  val up = new Up(KORE)

  def locationToAtt(l: Location): Att =
    Att(up(Location(l.startLine, l.startColumn, l.endLine, l.endColumn)))
}
