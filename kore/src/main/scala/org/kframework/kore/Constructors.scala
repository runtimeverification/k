package org.kframework.kore

import org.kframework.attributes._

trait Constructors {
  def KLabel(name: String): KLabel
  def Sort(name: String): Sort
  def KList(items: java.lang.Iterable[K]): KList
  def KToken(sort: Sort, s: String, att: Attributes): KToken
  def KApply(klabel: KLabel, klist: KList, att: Attributes): KApply
  def KSequence(left: K, right: K, att: Attributes): KSequence
  def KVariable(name: String, att: Attributes): KVariable
  def KRewrite(left: K, right: K, att: Attributes): KRewrite
}
