package org.kframework.tiny

import org.kframework.attributes._
import org.kframework.kore.{ADTConstructors => basic, InjectedKLabel, Unapply}
import org.kframework.{definition, kore, tiny}

import scala.collection.JavaConverters._

class Constructors(module: definition.Module) extends kore.Constructors {

  implicit val theory = FreeTheory

  override def KLabel(name: String): Label = {
    val att = module.attributesFor(basic.KLabel(name))
    if (att.contains("assoc"))
      RegularKAssocAppLabel(name, att)
    else
      RegularKAppLabel(name, att)
  }

  override def KApply(klabel: kore.KLabel, klist: kore.KList, att: Att): KApp = {
    val x: Label = convert(klabel)
    x(klist.items.asScala.toSeq map convert, att).asInstanceOf[KApp]
  }

  override def KSequence[KK <: kore.K](items: java.util.List[KK], att: Att): KSeq =
    KSeq(items.asScala.toSeq map convert, att).asInstanceOf[KSeq]

  override def KVariable(name: String, att: Att): KVar = KVar(name, att)

  override def Sort(name: String): kore.Sort = basic.Sort(name)

  override def KToken(sort: kore.Sort, s: String, att: Att): KTok = RegularKTok(sort, s)

  override def KRewrite(left: kore.K, right: kore.K, att: Att): kore.KRewrite = tiny.KRewrite(convert(left), convert
    (right), att)

  override def KList[KK <: kore.K](items: java.util.List[KK]): kore.KList = basic.KList(items)

  override def InjectedKLabel(klabel: kore.KLabel, att: Att): InjectedKLabel = InjectedLabel(convert(klabel), att)

  def convert(l: kore.KLabel): Label = l match {
    case l: Label => l
    case Unapply.KLabel(name) => KLabel(name)
  }
  def convert(k: kore.K): K = k match {
    case k: K => k
    case t@Unapply.KApply(label, list) => KApply(label, KList(list.asJava), t.att)
  }

  import Builtins._

  implicit def stringToToken(s: String) = KToken(String, s, Att())
  implicit def symbolToLabel(l: Symbol) = KLabel("'" + l.name)
  implicit def intToToken(n: Int): K = KToken(Int, n.toString, Att())

  implicit class KWithSeq(k: K) {
    def ~>(other: K) = KSeq(Seq(k, other), Att())
    def ==>(other: K) = KRewrite(k, other, Att())
  }

  implicit class KVarWithArrow(k: KVar) {
    def ->(other: K) = Binding(k, other)
  }

  implicit def Tuple2IsBinding(t: (K, K)) = Binding(t._1, t._2)
}
