package org.kframework.kore

import org.kframework.attributes.Att
import org.kframework.builtin.{KLabels, Sorts}
import org.kframework.kore

import scala.collection.JavaConverters._

trait ScalaSugar[K <: kore.K] {
  self: Constructors[K] =>

  implicit def stringToToken(s: String) = KToken(s, Sorts.String, Att())
  def stringToId(s: String): K = KToken(s, Sorts.Id, Att())
  implicit def symbolToLabel(l: Symbol) = KLabel(l.name)
  implicit def intToToken(n: Int): K = KToken(n.toString, Sorts.Int, Att())

  implicit class ApplicableKLabel(klabel: KLabel) {
    def apply(l: K*): K = KApply(klabel, l: _*)
  }

  implicit class ApplicableSymbol(klabel: Symbol) {
    def apply(l: K*): K = KApply(klabel, l: _*)
  }

  implicit class EnhancedK(k: K) {
    def ~>(other: K) = KSequence(Seq(k, other).asJava, Att())
    def ==>(other: K) = KRewrite(k, other, Att())
    def +(other: K) = KLabel("+")(k, other)
    def -(other: K) = KLabel("-")(k, other)
    def *(other: K) = KLabel("*")(k, other)
    def /(other: K) = KLabel("/")(k, other)
    def &(other: K) = KLabel("&")(k, other)
    def ~(other: K) = KLabel("~")(k, other)
    def &&(other: K) = KLabel(KLabels.AND)(k, other)
    def ||(other: K) = KLabel(KLabels.OR)(k, other)
  }

  def KList[KK <: K](ks: Seq[KK]): KList = KList(ks.asJava)
  def KApply[KK <: K](klabel: KLabel, ks: Seq[KK], att: Att = Att()): K = KApply(klabel, KList(ks), att)
}
