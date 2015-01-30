package org.kframework.attributes

import org.kframework.kore._

case class Attributes(att: Set[K]) extends AttributesToString {
  def getK(key: String): Option[K] = att.find {
    case t@KApply(KLabel(`key`), v) => true
  }
  def get[T](key: String): Option[T] = getK(key) map {
    case t: KToken => t.s.asInstanceOf[T]
    case _ => ???
  }
}

trait KeyWithType

object Attributes {
  def apply(atts: K*): Attributes = Attributes(atts.toSet)
}

trait AttributesToString {
  self: Attributes =>

  override def toString() =
    "[" +
      (this.filteredAtt map {
        case KApply(KLabel(keyName), KList(KToken(_, value))) => keyName + "(" + value + ")"
        case x => x.toString
      }).toList.sorted.mkString(" ") +
      "]"

  def postfixString = {
    if (filteredAtt.isEmpty) "" else (" " + toString())
  }

  lazy val filteredAtt: Set[K] = att filter { case KApply(KLabel("productionID"), _) => false; case _ => true } // TODO: remove along with KIL to KORE to KIL convertors
}