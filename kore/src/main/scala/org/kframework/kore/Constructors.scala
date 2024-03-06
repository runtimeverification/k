// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kore

import org.kframework.attributes._
import scala.collection.immutable
import scala.collection.JavaConverters._

trait Constructors {
  def KLabel(name: String, params: immutable.Seq[Sort]): KLabel
  def Sort(name: String, params: immutable.Seq[Sort]): Sort
  def KList(items: java.util.List[K]): KList
  def KToken(s: String, sort: Sort, att: Att): KToken
  def KApply(klabel: KLabel, klist: KList, att: Att): KApply
  def KSequence(items: java.util.List[K], att: Att): KSequence
  def KVariable(name: String, att: Att): KVariable
  def KRewrite(left: K, right: K, att: Att): KRewrite
  def KAs(pattern: K, alias: K, att: Att): KAs
  def InjectedKLabel(klabel: KLabel, att: Att): InjectedKLabel

  // Unfortunately, IntelliJ struggles to resolve variadic functions,
  // so we instead manually provide overloads for 0-5 elements below
  final def KLabel(name: String, params: Array[Sort]): KLabel =
    KLabel(name, params.to[immutable.Seq])
  final def KLabel(name: String): KLabel              = KLabel(name, immutable.Seq())
  final def KLabel(name: String, param: Sort): KLabel = KLabel(name, immutable.Seq(param))
  final def KLabel(name: String, param1: Sort, param2: Sort): KLabel =
    KLabel(name, immutable.Seq(param1, param2))
  final def KLabel(name: String, param1: Sort, param2: Sort, param3: Sort): KLabel =
    KLabel(name, immutable.Seq(param1, param2, param3))
  final def KLabel(name: String, param1: Sort, param2: Sort, param3: Sort, param4: Sort): KLabel =
    KLabel(name, immutable.Seq(param1, param2, param3, param4))
  final def KLabel(
      name: String,
      param1: Sort,
      param2: Sort,
      param3: Sort,
      param4: Sort,
      param5: Sort
  ): KLabel =
    KLabel(name, immutable.Seq(param1, param2, param3, param4, param5))

  final def Sort(name: String, params: Array[Sort]): Sort = Sort(name, params.to[immutable.Seq])
  final def Sort(name: String): Sort                      = Sort(name, immutable.Seq())
  final def Sort(name: String, param: Sort): Sort         = Sort(name, immutable.Seq(param))
  final def Sort(name: String, param1: Sort, param2: Sort): Sort =
    Sort(name, immutable.Seq(param1, param2))
  final def Sort(name: String, param1: Sort, param2: Sort, param3: Sort): Sort =
    Sort(name, immutable.Seq(param1, param2, param3))
  final def Sort(name: String, param1: Sort, param2: Sort, param3: Sort, param4: Sort): Sort =
    Sort(name, immutable.Seq(param1, param2, param3, param4))
  final def Sort(
      name: String,
      param1: Sort,
      param2: Sort,
      param3: Sort,
      param4: Sort,
      param5: Sort
  ): Sort = Sort(name, immutable.Seq(param1, param2, param3, param4, param5))

  final def KList(items: Array[K]): KList              = KList(items.toList.asJava)
  final def KList(items: immutable.Seq[K]): KList      = KList(items.asJava)
  final def KList(): KList                             = KList(immutable.Seq())
  final def KList(item: K): KList                      = KList(immutable.Seq(item))
  final def KList(item1: K, item2: K): KList           = KList(immutable.Seq(item1, item2))
  final def KList(item1: K, item2: K, item3: K): KList = KList(immutable.Seq(item1, item2, item3))
  final def KList(item1: K, item2: K, item3: K, item4: K): KList = KList(
    immutable.Seq(item1, item2, item3, item4)
  )
  final def KList(item1: K, item2: K, item3: K, item4: K, item5: K): KList = KList(
    immutable.Seq(item1, item2, item3, item4, item5)
  )

  final def KApply(klabel: KLabel, items: Array[K]): KApply =
    KApply(klabel, KList(items.toList.asJava), Att.empty)
  final def KApply(klabel: KLabel, items: immutable.Seq[K]): KApply =
    KApply(klabel, KList(items.asJava), Att.empty)
  final def KApply(klabel: KLabel): KApply          = KApply(klabel, immutable.Seq())
  final def KApply(klabel: KLabel, item: K): KApply = KApply(klabel, immutable.Seq(item))
  final def KApply(klabel: KLabel, item1: K, item2: K): KApply =
    KApply(klabel, immutable.Seq(item1, item2))
  final def KApply(klabel: KLabel, item1: K, item2: K, item3: K): KApply =
    KApply(klabel, immutable.Seq(item1, item2, item3))
  final def KApply(klabel: KLabel, item1: K, item2: K, item3: K, item4: K): KApply =
    KApply(klabel, immutable.Seq(item1, item2, item3, item4))
  final def KApply(klabel: KLabel, item1: K, item2: K, item3: K, item4: K, item5: K): KApply =
    KApply(klabel, immutable.Seq(item1, item2, item3, item4, item5))

  final def KSequence(list: Array[K]): KSequence         = KSequence(list.toList.asJava, Att.empty)
  final def KSequence(list: immutable.Seq[K]): KSequence = KSequence(list.toList.asJava, Att.empty)
  final def KSequence(): KSequence                       = KSequence(immutable.Seq())
  final def KSequence(item: K): KSequence                = KSequence(immutable.Seq(item))
  final def KSequence(item1: K, item2: K): KSequence     = KSequence(immutable.Seq(item1, item2))
  final def KSequence(item1: K, item2: K, item3: K): KSequence = KSequence(
    immutable.Seq(item1, item2, item3)
  )
  final def KSequence(item1: K, item2: K, item3: K, item4: K): KSequence = KSequence(
    immutable.Seq(item1, item2, item3, item4)
  )
  final def KSequence(item1: K, item2: K, item3: K, item4: K, item5: K): KSequence = KSequence(
    immutable.Seq(item1, item2, item3, item4, item5)
  )

  final def KVariable(name: String): KVariable = KVariable(name, Att.empty)

  def convert(l: KLabel): KLabel = l match {
    case Unapply.KLabel(name) => KLabel(name)
  }

  def convert(k: K): K = k match {
    case t @ Unapply.KVariable(name)       => KVariable(name, t.att)
    case t @ Unapply.KToken(v, s)          => KToken(v, s, t.att)
    case t @ Unapply.KRewrite(left, right) => KRewrite(convert(left), convert(right), t.att)
    case t @ Unapply.KSequence(s)          => KSequence(s.map(convert).asJava, t.att)
    case t @ Unapply.KApply(label, list)   => KApply(label, KList(list.map(convert).asJava), t.att)
  }
}
