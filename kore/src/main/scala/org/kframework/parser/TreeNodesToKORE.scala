package org.kframework.parser

import java.util

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
    case c@Constant(s, p) => KToken(p.sort, s, locationToAtt(c.location.get(), c.source.get()))
    case t@TermCons(items, p) => KApply(p.klabel.get, KList(new util.ArrayList(items).asScala.reverse map apply asJava), locationToAtt(t.location.get(), t.source.get()))
    case Ambiguity(items) => KApply(KLabel("AMB"), KList(items.asScala.toList map apply asJava), Att())
  }

  def down(t: K): K = t match {
    case t@KToken(sort, s) if sort == Sorts.KVariable =>
      KVariable(s.trim, t.att)

    case t: kore.KToken => t

    case t@KApply(KLabel("#KSequence"), items) =>
      KSequence(downList(items).asJava, t.att)
    case KApply(KLabel("#EmptyK"), items) if items.isEmpty =>
      KSequence(List.empty[K].asJava, t.att)

    case t@KApply(KLabel("#KRewrite"), items) =>
      val it = items.iterator
      val res = KRewrite(down(it.next()), down(it.next()), t.att)
      assert(!it.hasNext)
      res


    case t@KApply(KLabel("#KApply"), items) =>
      KApply(downKLabel(items(0)),
        KList(downList(Assoc.flatten(KLabel("#KList"), items, KLabel("#EmptyKList")))), t.att)

    case t@KApply(KLabel("#KToken"), items) =>
      def removeQuotes(s: String) = s.drop(1).dropRight(1)

      KToken(Sort(removeQuotes(items(0).asInstanceOf[Constant].value)),
        removeQuotes(items.tail.head.asInstanceOf[Constant].value))

    case t@KApply(l, items) =>
      KApply(l, KList((items map down _).asJava), t.att)
  }

  def unquote(t: K): String = {
    t.asInstanceOf[KToken].s.stripPrefix("`").stripSuffix("`")
  }

  def downList(items: Seq[K]): Seq[K] = {
    items map down _
  }

  def downKLabel(t: K): KLabel = t match {
    case t@KToken(sort, s) if sort == Sorts.KVariable =>
      KVariable(s.trim, t.att)

    case t@KToken(sort, s) if sort == Sorts.KLabel =>
      KLabel(unquote(t))

    case t@KApply(KLabel(s), items) if s.startsWith("#SemanticCastTo") =>
      downKLabel(items.head)
  }

  val up = new Up(KORE, Set())

  def locationToAtt(l: Location, s: Source): Att =
    Att(up(Location(l.startLine, l.startColumn, l.endLine, l.endColumn)), up(Source(s.source)))
}
