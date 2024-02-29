// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kore

import org.kframework.attributes
import org.kframework.attributes.Att
import org.kframework.builtin.KLabels
import scala.collection.{ IndexedSeq => _, Seq => _, _ }
import scala.collection.JavaConverters._

/**
 * Basic implementation of a Constructor of inner KORE classes. It can be used by either creating a
 * KORE object, or by importing the class statically.
 *
 * See the wiki for more details:
 * https://github.com/runtimeverification/k/wiki/KORE-data-structures-guide
 */
object KORE extends Constructors {
  val constructor = this

  def Location(startLine: Int, startColumn: Int, endLine: Int, endColumn: Int) =
    attributes.Location(startLine, startColumn, endLine, endColumn)

  def KApply(klabel: KLabel, klist: KList): KApply = KApply(klabel, klist, Att.empty)

  def KApply(klabel: KLabel, ks: Seq[K], att: Att = Att.empty): KApply =
    KApply(klabel, KList(ks.asJava), att)

  def KToken(string: String, sort: Sort): KToken = KToken(string, sort, Att.empty)

  def KSequence(ks: java.util.List[K]): KSequence = KSequence(ks, Att.empty)

  def KRewrite(left: K, right: K): KRewrite = KRewrite(left, right, Att.empty)

  def KAs(pattern: K, alias: K): KAs = KAs(pattern, alias, Att.empty)

  def InjectedKLabel(label: KLabel): InjectedKLabel = InjectedKLabel(label, Att.empty)

  //  def toKList: Collector[K, KList] =
  //    Collector(() => new CombinerFromBuilder(KList.newBuilder()))

  //  def toKSequence: Collector[K, KSequence] =
  //    Collector(() => new CombinerFromBuilder(KSequence.newBuilder()))

  override def KLabel(name: String, params: Seq[Sort]): KLabel = ADT.KLabel(name, params: _*)

  override def KApply(klabel: KLabel, klist: KList, att: Att): KApply =
    ADT.KApply(klabel, klist, att)

  override def KSequence(items: java.util.List[K], att: Att): KSequence =
    ADT.KSequence(items.asScala.toList, att)

  override def KVariable(name: String, att: Att): KVariable = ADT.KVariable(name, att)

  override def Sort(name: String, params: Seq[Sort]): Sort = ADT.Sort(name, params: _*)

  def Sort(name: SortHead): Sort = {
    assert(name.params == 0)
    ADT.Sort(name.name)
  }

  def Sort(name: String, params: java.util.List[Sort]): Sort = ADT.Sort(name, params.asScala: _*)

  def SortHead(name: String, params: Int): SortHead = ADT.SortHead(name, params)

  override def KToken(s: String, sort: Sort, att: Att): KToken = ADT.KToken(s, sort, att)

  override def KRewrite(left: K, right: K, att: Att): KRewrite = ADT.KRewrite(left, right, att)

  override def KAs(pattern: K, alias: K, att: Att): KAs = ADT.KAs(pattern, alias, att)

  override def KList(items: java.util.List[K]): KList = ADT.KList(items.asScala.toList)

  def KList(items: List[K]): KList = ADT.KList(items)

  override def InjectedKLabel(klabel: KLabel, att: Att): InjectedKLabel =
    ADT.InjectedKLabel(klabel, att)

  def self = this

  object Sugar {
    def ~>(l: K, r: K): KSequence = KSequence(Seq(l, r).asJava, Att.empty)

    def +(l: K, r: K): KApply = KApply(KLabel("+"), l, r)

    def -(l: K, r: K): KApply = KApply(KLabel("-"), l, r)

    def *(l: K, r: K): KApply = KApply(KLabel("*"), l, r)

    def /(l: K, r: K): KApply = KApply(KLabel("/"), l, r)

    def &(l: K, r: K): KApply = KApply(KLabel("&"), l, r)

    def ~(l: K, r: K): KApply = KApply(KLabel("~"), l, r)

    def &&(l: K, r: K): KApply = KApply(KLabels.AND, l, r)

    def ||(l: K, r: K): KApply = KApply(KLabels.OR, l, r)
  }
}
