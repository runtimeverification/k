package org.kframework.kore

import org.kframework.attributes._

import scala.collection.JavaConverters._

trait Constructors[KK <: K] {
  def KLabel(name: String): KLabel
  def Sort(name: String): Sort
  def KList[KKK <: KK](items: java.util.List[KKK]): KList
  def KToken(sort: Sort, s: String, att: Att): KToken with KK
  def KApply(klabel: KLabel, klist: KList, att: Att): KApply with KK
  def KSequence[KKK <: KK](items: java.util.List[KKK], att: Att): KSequence with KK
  def KVariable(name: String, att: Att): KVariable with KK
  def KRewrite(left: K, right: K, att: Att): KRewrite with KK
  def InjectedKLabel(klabel: KLabel, att: Att): InjectedKLabel

  val injectedKListLabel = "INJECTED-KLIST"

  // default methods:
  @annotation.varargs def KList[KKK <: KK](items: KKK*): KList = KList(items.asJava)
  @annotation.varargs def KApply(klabel: KLabel, items: KK*): KApply with KK = KApply(klabel, KList(items.asJava), Att())
  @annotation.varargs def KSequence(list: KK*): KSequence with KK = KSequence(list.toList.asJava, Att())
  def KVariable(name: String): KVariable with KK = KVariable(name, Att())
}

abstract class AbstractConstructors[KK <: K] extends Constructors[KK]


