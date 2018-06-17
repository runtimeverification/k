package org.kframework.kore

import org.kframework.attributes._

import scala.collection.JavaConverters._

trait Constructors {
  def KLabel(name: String, params: Sort*): KLabel
  def Sort(name: String, params: Sort*): Sort
  def KList(items: java.util.List[K]): KList
  def KToken(s: String, sort: Sort, att: Att): KToken
  def KApply(klabel: KLabel, klist: KList, att: Att): KApply
  def KSequence(items: java.util.List[K], att: Att): KSequence
  def KVariable(name: String, att: Att): KVariable
  def KRewrite(left: K, right: K, att: Att): KRewrite
  def KAs(pattern: K, alias: K, att: Att): KAs
  def InjectedKLabel(klabel: KLabel, att: Att): InjectedKLabel

  // default methods:
  @annotation.varargs def KList(items: K*): KList = KList(items.asJava)
  @annotation.varargs def KApply(klabel: KLabel, items: K*): KApply = KApply(klabel, KList(items.asJava), Att.empty)
  @annotation.varargs def KSequence(list: K*): KSequence = KSequence(list.toList.asJava, Att.empty)
  def KVariable(name: String): KVariable = KVariable(name, Att.empty)

  def convert(l: KLabel): KLabel = l match {
    case Unapply.KLabel(name) => KLabel(name)
  }

  def convert(k: K): K  = k match {
    case t@Unapply.KVariable(name) => KVariable(name, t.att)
    case t@Unapply.KToken(v, s) => KToken(v, s, t.att)
    case t@Unapply.KRewrite(left, right) => KRewrite(convert(left), convert(right), t.att)
    case t@Unapply.KSequence(s) => KSequence((s map convert).asJava, t.att)
    case t@Unapply.KApply(label, list) => KApply(label, KList((list map convert).asJava), t.att)
  }
}

abstract class AbstractConstructors extends Constructors

