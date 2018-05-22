package org.kframework.kore

import org.kframework.attributes.Att
import org.kframework.builtin.{KLabels, Sorts}
import org.kframework.kore

import scala.collection.JavaConverters._

trait ScalaSugared {
  val c: Constructors

  import c._

  implicit def stringToToken(s: String) = KToken(s, Sorts.String, Att.empty)
  def stringToId(s: String): K = KToken(s, Sorts.Id, Att.empty)
  implicit def symbolToLabel(l: Symbol) = KLabel(l.name)
  implicit def intToToken(n: Int): K = KToken(n.toString, Sorts.Int, Att.empty)

  implicit class ApplicableKLabel(klabel: KLabel) {
    def apply(l: K*): K = c.KApply(klabel, l: _*)
  }

  implicit class EnhancedK(k: K) {
    def ~>(other: K) = KSequence(Seq(k, other).asJava, Att.empty)
    def ==>(other: K) = KRewrite(k, other, Att.empty)
    def +(other: K) = KLabel("+")(k, other)
    def -(other: K) = KLabel("-")(k, other)
    def *(other: K) = KLabel("*")(k, other)
    def /(other: K) = KLabel("/")(k, other)
    def &(other: K) = KLabel("&")(k, other)
    def ~(other: K) = KLabel("~")(k, other)
    def &&(other: K) = KLabels.AND.apply(k, other)
    def ||(other: K) = KLabels.OR.apply(k, other)
  }

  def KList(ks: Seq[K]): KList = c.KList(ks.asJava)

  def KApply(klabel: KLabel, ks: Seq[K], att: Att = Att.empty): KApply = c.KApply(klabel, c.KList(ks.asJava), att)
}
