package org.kframework.kore

import org.kframework.attributes._


trait Constructors {
  def KLabel(name: String): KLabel
  def Sort(name: String): Sort
  def KList[KK <: K](items: java.util.List[KK]): KList
  def KToken(sort: Sort, s: String, att: Att): KToken
  def KApply(klabel: KLabel, klist: KList, att: Att): KApply
  def KSequence[KK <: K](items: java.util.List[KK], att: Att): KSequence
  def KVariable(name: String, att: Att): KVariable
  def KRewrite(left: K, right: K, att: Att): KRewrite
  def InjectedKLabel(klabel: KLabel, att: Att): InjectedKLabel

  val injectedKListLabel = "INJECTED-KLIST"
}


