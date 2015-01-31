package org.kframework.tiny

import org.kframework.attributes._
import org.kframework.kore.{ADTConstructors => basic, InjectedKLabel, Unapply}
import org.kframework.{definition, kore, tiny}

import scala.collection.JavaConverters._

class Constructors(module: definition.Module) extends kore.Constructors {

  implicit val theory = FreeTheory

  override def KLabel(name: String): Label[KApp] = {
    val att = module.attributesFor(basic.KLabel(name))
    if (att.contains("assoc"))
      AssocKAppLabel(name, att)
    else
      RegularKAppLabel(name, att)
  }

  override def KApply(klabel: kore.KLabel, klist: kore.KList, att: Att): KApp = {
    val x: Label[KApp] = convert(klabel)
    x(klist.items.asScala.toSeq map convert, att).asInstanceOf[KApp]
  }

  override def KSequence[KK <: kore.K](items: java.util.List[KK], att: Att): KSeq =
    KSeq(items.asScala.toSeq map convert, att).asInstanceOf[KSeq]

  override def KVariable(name: String, att: Att): KVar = KVar(name, att)

  override def Sort(name: String): kore.Sort = basic.Sort(name)

  override def KToken(sort: kore.Sort, s: String, att: Att): kore.KToken = KTok(sort, s)

  override def KRewrite(left: kore.K, right: kore.K, att: Att): kore.KRewrite = tiny.KRewrite(convert(left), convert(right), att)

  override def KList[KK <: kore.K](items: java.util.List[KK]): kore.KList = basic.KList(items)

  override def InjectedKLabel(klabel: kore.KLabel, att: Att): InjectedKLabel = InjectedLabel(convert(klabel), att)

  def convert(l: kore.KLabel): Label[KApp] = l match {
    case l: Label[KApp] => l
    case Unapply.KLabel(name) => KLabel(name)
  }
  def convert(k: kore.K): K = k match {
    case k: K => k
    case t@Unapply.KApply(label, list) => KApply(label, KList(list.asJava), t.att)
  }
}
