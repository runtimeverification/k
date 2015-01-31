// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.koreimplementation

;

import org.kframework._
import org.kframework.attributes.Attributes
import org.kframework.kore.Sort

import scala.collection.JavaConverters._

/**
 *
 * Helper constructors for KORE classes. The class is meant to be imported
 * statically.
 *
 * @see org.kframework.koreimplementation.InterfaceTest
 *
 */

object Constructors extends kore.Constructors {
  def Attributes(ks: Set[K]) = attributes.Attributes(ks.toSeq: _*)
  @annotation.varargs def Attributes(ks: K*) = attributes.Attributes(ks: _*)

  //  @annotation.varargs def KBag(ks: K*) = koreimplementation.KBag(ks)

  def Location(startLine: Int, startColumn: Int, endLine: Int, endColumn: Int) = attributes.Location(startLine, startColumn, endLine, endColumn)

  //  def KBag(ks: KList) = koreimplementation.KBag(ks);

  def Sort(name: String) = koreimplementation.Sort(name);

  def KLabel(name: String) = koreimplementation.KLabel(name);

  @annotation.varargs def KList(ks: K*): KList = koreimplementation.KList(ks)

  //  def KList(ks: java.lang.Iterable[K]): KList =
  override def KList[KK <: kore.K](ks: java.util.List[KK]): koreimplementation.KList =
    koreimplementation.KList(ks.asScala.map(convert))


  def KApply(klabel: KLabel, klist: KList, att: attributes.Attributes) = koreimplementation.KApply(klabel, klist, att)

  def KApply(klabel: KLabel, klist: KList) = koreimplementation.KApply(klabel, klist, Attributes())

  def KToken(sort: Sort, string: String, att: attributes.Attributes) = koreimplementation.KToken(sort, string, att)
  def KToken(sort: Sort, string: String) = koreimplementation.KToken(sort, string, Attributes())

  def KVariable(name: String, att: attributes.Attributes) = koreimplementation.KVariable(name, att)

  def KVariable(name: String) = {
    koreimplementation.KVariable(name, Attributes())
  }

  def InjectedKLabel(l: kore.KLabel, att: Attributes) = koreimplementation.InjectedKLabel(convert(l))

  def InjectedKList(l: KList) = koreimplementation.InjectedKList(l)

  @annotation.varargs def KSequence(ks: K*) = koreimplementation.KSequence(ks: _*)

  def KSequence(ks: java.util.List[K]) = koreimplementation.KSequence(ks.asScala.toList)

  def KRewrite(left: K, right: K) = koreimplementation.KRewrite(left, right, Attributes())

  def KRewrite(left: K, right: K, att: attributes.Attributes) = koreimplementation.KRewrite(left, right, att)

  //  def KInt(n: Int) = koreimplementation.KInt(n)

//  def stream(c: KCollection) = org.kframework.Collections.stream(c);

  def toKList: Collector[K, KList] =
    Collector(() => new CombinerFromBuilder(koreimplementation.KList.newBuilder()))

  def toKSequence: Collector[K, KSequence] =
    Collector(() => new CombinerFromBuilder(koreimplementation.KSequence.newBuilder()))


  override def KApply(klabel: kore.KLabel, klist: kore.KList, att: Attributes): kore.KApply = ???
  override def KSequence[KK <: kore.K](items: java.util.List[KK], att: Attributes): kore.KSequence = ???
  override def KRewrite(left: kore.K, right: kore.K, att: Attributes): kore.KRewrite = ???

  def convert(klist: kore.KList): koreimplementation.KList = klist match {
    case l: koreimplementation.KList => l
    case l => koreimplementation.KList(l.items.asScala.map(convert))
  }

  def convert(label: kore.KLabel): koreimplementation.KLabel = label match {
    case l: koreimplementation.KLabel => l
    case l => KLabel(l.name)
  }

  def convert(k: kore.K): koreimplementation.K = k match {
    case k: koreimplementation.K => k
    case k => k match {
      case t@kore.Unapply.KApply(label, klist) => KApply(convert(label), KList(klist.asJava), t.att)
      case t@kore.Unapply.KToken(sort, s) => KToken(sort, s, t.att)
    }
  }
}
