package org.kframework.tiny

import org.kframework.attributes._
import org.kframework.kore.{Constructors => basic, InjectedKLabel, KORE, Unapply}
import org.kframework.{definition, kore, tiny}

import scala.collection.JavaConverters._

class Constructors(module: definition.Module) extends kore.Constructors {

  implicit val theory = FreeTheory

  override def KLabel(name: String): Label = {

    if (name.startsWith("'<")) {
      RegularKAssocAppLabel(name, Att())
    } else {
      if(name == "'_=[];")
        println(module.attributesFor)
      val att = module.attributesFor(KORE.KLabel(name))

      if (att.contains("assoc"))
        RegularKAssocAppLabel(name, att)
      else
        RegularKAppLabel(name, att)
    }
  }

  override def KApply(klabel: kore.KLabel, klist: kore.KList, att: Att): KApp = {
    val x: Label = convert(klabel)
    x(klist.items.asScala.toSeq map convert, att).asInstanceOf[KApp]
  }

  def KApply(klabel: kore.KLabel, list: List[tiny.K], att: Att): KApp = {
    val x: Label = convert(klabel)
    x(list, att).asInstanceOf[KApp]
  }

  def KApply(klabel: kore.KLabel, list: List[tiny.K]): KApp = KApply(klabel, list, Att())

  @annotation.varargs def KApply(klabel: kore.KLabel, list: K*): KApp = KApply(klabel, list.toList)

  override def KSequence[KK <: kore.K](items: java.util.List[KK], att: Att): KSeq =
    KSeq(items.asScala.toSeq map convert, att).asInstanceOf[KSeq]

  override def KVariable(name: String, att: Att): KVar = KVar(name, att)

  override def Sort(name: String): kore.Sort = KORE.Sort(name)

  override def KToken(sort: kore.Sort, s: String, att: Att): KTok = RegularKTok(sort, s)

  override def KRewrite(left: kore.K, right: kore.K, att: Att) = tiny.KRewrite(convert(left), convert
    (right), att)

  override def KList[KK <: kore.K](items: java.util.List[KK]): kore.KList = KORE.KList(items)

  override def InjectedKLabel(klabel: kore.KLabel, att: Att): InjectedKLabel = InjectedLabel(convert(klabel), att)

  def convert(l: kore.KLabel): Label = l match {
    case l: Label => l
    case Unapply.KLabel(name) => KLabel(name)
  }
  def convert(k: kore.K): tiny.K = k match {
    case k: K => k
    case t@Unapply.KVariable(name) => KVariable(name, t.att)
    case t@Unapply.KToken(s, v) => KToken(s, v, t.att)
    case t@Unapply.KRewrite(left, right) => KRewrite(convert(left), convert(right), t.att)
    case t@Unapply.KSequence(s) => KSequence((s map convert).asJava, t.att)
    case t@Unapply.KApply(label, list) => KApply(label, KList((list map convert).asJava), t.att)
  }

  import org.kframework.tiny.Builtins._

  implicit def stringToToken(s: String) = KToken(String, s, Att())
  implicit def stringToId(s: String) = KToken(Id, s, Att())
  implicit def symbolToLabel(l: Symbol) = KLabel(l.name)
  implicit def intToToken(n: Int): K = KToken(Int, n.toString, Att())

  implicit class EnhancedK(k: K) {
    def ~>(other: K) = KSeq(Seq(k, other), Att())
    def ==>(other: K): KRewrite = KRewrite(k, other, Att())
    def +(other: K) = KLabel("+")(k, other)
    def &&(other: K) = And(k, other)
    def ||(other: K) = Or(k, other)
  }

  implicit class KVarWithArrow(k: KVar) {
    def ->(other: K) = Binding(k, other)
  }

  implicit def Tuple2IsBinding(t: (K, K)) = Binding(t._1, t._2)

  @annotation.varargs def Att(ks: K*) = org.kframework.attributes.Att(ks: _*)
}
