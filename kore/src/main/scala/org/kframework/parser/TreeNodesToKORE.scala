// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser

import java.util
import java.util.Optional
import org.kframework.{ kore => k }
import org.kframework.attributes.Att
import org.kframework.attributes.Location
import org.kframework.attributes.Source
import org.kframework.builtin.Sorts
import org.kframework.definition.Production
import org.kframework.kore._
import org.kframework.kore.Unapply._
import org.kframework.utils.errorsystem.KEMException
import scala.collection.immutable
import scala.collection.JavaConverters._

class TreeNodesToKORE(parseSort: java.util.function.Function[String, Sort]) {

  import org.kframework.kore.KORE.InjectedKLabel
  import org.kframework.kore.KORE.KApply
  import org.kframework.kore.KORE.KAs
  import org.kframework.kore.KORE.KLabel
  import org.kframework.kore.KORE.KList
  import org.kframework.kore.KORE.KRewrite
  import org.kframework.kore.KORE.KSequence
  import org.kframework.kore.KORE.KToken
  import org.kframework.kore.KORE.KVariable

  def apply(t: Term): K = t match {
    case c @ Constant(s, p) =>
      KToken(
        s,
        p.sort,
        locationToAtt(c.location, c.source)
          .add(
            Att.PRODUCTION,
            classOf[Production],
            c.production.att
              .getOption(Att.ORIGINAL_PRD, classOf[Production])
              .getOrElse(c.production)
          )
      )
    case t @ TermCons(_, _) => termConsToKApply(t)
    case Ambiguity(items) =>
      KApply(KLabel("amb"), KList(items.asScala.toList.map(apply).asJava), Att.empty)
  }

  def termConsToKApply(t: TermCons): K = {
    val realProd =
      if (t.production.att.contains(Att.ORIGINAL_PRD, classOf[Production]))
        t.production.att.get(Att.ORIGINAL_PRD, classOf[Production])
      else t.production
    if (t.production.att.contains(Att.BRACKET))
      return apply(t.items.get(0))
    if (t.production.klabel.isEmpty)
      throw KEMException.internalError("Missing klabel in production: " + t.production, t)
    val klabel =
      if (t.production.klabel.get.name == "#OuterCast")
        KLabel("project:" ++ t.production.sort.toString)
      else t.production.klabel.get
    KApply(
      klabel.head,
      KList(new util.ArrayList(t.items).asScala.reverse.map(apply).asJava),
      locationToAtt(t.location, t.source).add(Att.PRODUCTION, classOf[Production], realProd)
    )
  }

  def down(t: K): K = t match {
    case t @ KToken(s, sort) if sort == Sorts.KVariable =>
      KVariable(s.trim, t.att)

    case t: k.KToken => t

    case t @ KApply(KLabel("#KSequence"), items) =>
      KSequence(downList(items).asJava, t.att)
    case KApply(KLabel("#EmptyK"), items) if items.isEmpty =>
      KSequence(List.empty[K].asJava, t.att)

    case t @ KApply(KLabel("#KRewrite"), items) =>
      val it  = items.iterator
      val res = KRewrite(down(it.next()), down(it.next()), t.att)
      assert(!it.hasNext)
      res

    case t @ KApply(KLabel("#KApply"), items) =>
      KApply(
        downKLabel(items(0)),
        KList(downList(Assoc.flatten(KLabel("#KList"), items.tail, KLabel("#EmptyKList")))),
        t.att
      )

    case t @ KApply(KLabel("#KAs"), items) =>
      val it  = items.iterator
      val res = KAs(down(it.next()), down(it.next()), t.att)
      assert(!it.hasNext)
      res

    case t @ KApply(KLabel("#WrappedKLabel"), items) =>
      InjectedKLabel(downKLabel(items(0)), t.att)

    case t @ KApply(KLabel("#KToken"), items) =>
      def removeQuotes(s: String) = s.drop(1).dropRight(1).replace("\\\"", "\"")

      KToken(
        removeQuotes(items.head.asInstanceOf[KToken].s),
        parseSort(removeQuotes(items.tail.head.asInstanceOf[KToken].s)),
        t.att
      )

    case t @ KApply(l, items) =>
      KApply(l, KList(items.map(down _).asJava), t.att)
  }

  def unquote(t: K): String =
    t.asInstanceOf[KToken].s.stripPrefix("`").stripSuffix("`")

  def downList(items: immutable.Seq[K]): immutable.Seq[K] =
    items.map(down _)

  def downKLabel(t: K): KLabel = t match {
    case t @ KToken(s, sort) if sort == Sorts.KLabel =>
      KLabel(unquote(t))
  }

  def locationToAtt(l: Optional[Location], s: Optional[Source]): Att = {
    var a = Att.empty
    if (l.isPresent) a = a.add(Att.LOCATION, classOf[Location], l.get)
    if (s.isPresent) a = a.add(Att.SOURCE, classOf[Source], s.get)
    a
  }
}
