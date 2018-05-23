package org.kframework.parser

import java.util

import org.kframework.attributes._
import org.kframework.builtin.Sorts
import org.kframework.definition.{NonTerminal, Production}
import org.kframework.kore
import org.kframework.kore.Unapply._
import org.kframework.kore.{KORE, _}
import org.pcollections.PStack

import scala.collection.JavaConverters._

class TreeNodesToKORE(parseSort: java.util.function.Function[String, Sort]) {

  import org.kframework.kore.KORE._

  def apply(t: Term): K = t match {
    case c@Constant(s, p) => KToken(s, p.sort, locationToAtt(c.location.get(), c.source.get()))
    case t@TermCons(items, p) => termConsToKApply(t, items, p)
    case Ambiguity(items) => KApply(KLabel("AMB"), KList(items.asScala.toList map apply asJava), Att)
  }

  def termConsToKApply(t: TermCons, items: PStack[Term], p: Production): KApply = {
    if (p.att.contains("recordPrd", classOf[Production])) {
      val realProd = p.att.get("recordPrd", classOf[Production])
      val map = new util.ArrayList(items).asScala.reverse.zipWithIndex.map { case (item, idx) => (p.nonterminal(idx).name.get, apply(item))} toMap
      val realItems = realProd.nonterminals.map {
        case NonTerminal(_, None) => KToken("_", Sorts.KVariable)
        case NonTerminal(_, Some(x)) => map.getOrElse(x, KToken("_", Sorts.KVariable))
      }
      KApply(p.klabel.get, KList(realItems.asJava), locationToAtt(t.location.get(), t.source.get()).add(classOf[Production], realProd))
    } else
      KApply(p.klabel.get, KList(new util.ArrayList(items).asScala.reverse map apply asJava), locationToAtt(t.location.get(), t.source.get()).add(classOf[Production], p))
  }

  def down(t: K): K = t match {
    case t@KToken(s, sort) if sort == Sorts.KVariable =>
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
        KList(downList(Assoc.flatten(KLabel("#KList"), items.tail, KLabel("#EmptyKList")))), t.att)

    case t@KApply(KLabel("#KAs"), items) =>
      val it = items.iterator
      val res = KAs(down(it.next()), down(it.next()), t.att)
      assert(!it.hasNext)
      res

    case t@KApply(KLabel("#WrappedKLabel"), items) =>
      InjectedKLabel(downKLabel(items(0)), t.att)

    case t@KApply(KLabel("#KToken"), items) =>
      def removeQuotes(s: String) = s.drop(1).dropRight(1).replace("\\\"", "\"")

      KToken(removeQuotes(items.head.asInstanceOf[KToken].s), parseSort(removeQuotes(items.tail.head.asInstanceOf[KToken].s)))

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
    case t@KToken(s, sort) if sort == Sorts.KVariable =>
      KVariable(s.trim, t.att)

    case t@KToken(s, sort) if sort == Sorts.KLabel =>
      KLabel(unquote(t))

    case t@KApply(KLabel(s), items) if s.startsWith("#SemanticCastTo") =>
      downKLabel(items.head)
  }

  def locationToAtt(l: Location, s: Source): Att =
    Att.add(classOf[Location], l).add(classOf[Source], s)
}
