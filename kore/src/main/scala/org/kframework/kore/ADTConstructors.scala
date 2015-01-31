package org.kframework.kore

import org.kframework.attributes._
import collection.JavaConverters._

object ADTConstructors extends Constructors {
  override def KLabel(name: String): KLabel = ADT.KLabel(name)

  override def KApply(klabel: KLabel, klist: KList, att: Att): KApply = ADT.KApply(klabel, klist, att)

  override def KSequence[KK <: K](items: java.util.List[KK], att: Att): KSequence = ADT.KSequence(items.asScala.toList, att)

  override def KVariable(name: String, att: Att): KVariable = ADT.KVariable(name, att)

  override def Sort(name: String): Sort = ADT.Sort(name)

  override def KToken(sort: Sort, s: String, att: Att): KToken = ADT.KToken(sort, s, att)

  override def KRewrite(left: K, right: K, att: Att): KRewrite = ADT.KRewrite(left, right, att)

  override def KList[KK <: K](items: java.util.List[KK]): KList = ADT.KList(items.asScala.toList)

  override def InjectedKLabel(klabel: KLabel, att: Att): InjectedKLabel = ADT.InjectedKLabel(klabel, att)

  def KList(ks: K*): KList = ADT.KList(ks.toList)
}

