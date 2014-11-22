package org.kframework.kore

case class Attributes(att: Set[K] = Set()) extends AttributesToString {
  def contains(label: String): Boolean = (att find {
    case KApply(KLabel(label), _, _) => true
    case _ => false
  }) != None

  def get(label: String): K = KList(att collect {
    case KApply(KLabel(label), value, _) => value
  } toList: _*) match {
    case KList(e) => e
    case e => e
  }
}

object Attributes {
  def apply(ks: K*) = new Attributes(ks.toSet)
}
