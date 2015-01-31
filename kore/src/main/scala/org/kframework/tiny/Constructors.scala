package org.kframework.tiny

import org.kframework.attributes._
import org.kframework.kore.{ADTConstructors => basic, Unapply, InjectedKLabel}
import org.kframework.{kore, definition}
import collection.JavaConverters._

class Constructors(module: definition.Module) extends kore.Constructors {

  override def KLabel(name: String): Label[KApp] = {
    val att = module.attributesFor(basic.KLabel(name))
    if (att.contains("assoc"))
      AssocKApplyLabel(name, att)
    else
      RegularKApplyLabel(name, att)
  }

  override def KApply(klabel: kore.KLabel, klist: kore.KList, att: Att): KApp = {
    val x: Label[KApp] = convert(klabel)
    x(klist.items.asScala.toSeq map convert, att)
  }

  override def KSequence[KK <: kore.K](items: java.util.List[KK], att: Att): KSeq =
    KSeq(items.asScala.toSeq map convert, att)

  override def KVariable(name: String, att: Att): KVar = KVar(name, att)

  override def Sort(name: String): kore.Sort = ???
  override def KToken(sort: kore.Sort, s: String, att: Att): kore.KToken = ???
  override def KRewrite(left: kore.K, right: kore.K, att: Att): kore.KRewrite = ???
  override def KList[KK <: kore.K](items: java.util.List[KK]): kore.KList = ???
  override def InjectedKLabel(klabel: kore.KLabel, att: Att): InjectedKLabel = ???

  def convert(l: kore.KLabel): Label[KApp] = l match {
    case l: Label[KApp] => l
    case Unapply.KLabel(name) => KLabel(name)
  }
  def convert(k: kore.K): K = k match {
    case k: K => k
    case t@Unapply.KApply(label, list) => KApply(label, KList(list.asJava), t.att)
  }
}
