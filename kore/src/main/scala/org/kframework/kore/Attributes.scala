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

  def add(that: Attributes) = Attributes(att ++ that.att)
}

object Attributes {
  def apply(ks: K*) = new Attributes(ks.toSet)
}

trait AttributesToString {
  self: Attributes =>

  override def toString() = "[" +
    (att map {
      case KApply(KLabel(keyName), KList(KToken(_, KString(value), _)), _) => keyName + "(" + value + ")"
      // FIXME: This is to prevent printing metadata saved as attributes. Currently this metadata
      // is used to guide translating KORE back to KIL.
      case a => a.toString
    }).toList.sorted.mkString(" ") +
    "]" // TODO: remove brackets if nothing is printed inside

  def postfixString = if (att.isEmpty) "" else (" " + toString())
}
