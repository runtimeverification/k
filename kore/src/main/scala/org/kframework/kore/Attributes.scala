package org.kframework.kore

import scala.collection.mutable.SetBuilder
import scala.collection.mutable.Builder

case class Attributes(att: Set[K] = Set()) extends Collection[K] with Indexed[String, KList] with AttributesToString {
  type This = Attributes

  def contains(label: String): Boolean = (att find {
    case KApply(KLabel(label), _, _) => true
    case _ => false
  }) != None

  def get(label: String): Option[KList] = att collect {
    case KApply(KLabel(`label`), l, _) => l
  } headOption

  def add(that: Attributes) = Attributes(att ++ that.att)

  def foreach(f: K => Unit): Unit = att foreach f

  def iterable: Iterable[K] = att

  def newBuilder: Builder[K, Attributes] = new SetBuilder[K, Set[K]](Set()) mapResult { new Attributes(_) }
}

object Attributes {
  def apply(ks: K*) = new Attributes(ks.toSet)
}

trait AttributesToString {
  self: Attributes =>

  override def toString() =
    "[" +
    (this map[String] {
      case KApply(KLabel(keyName), KList(KToken(_, KString(value), _)), _) => keyName + "(" + value + ")"
      case x => x.toString
    }).sorted.mkString(" ") +
    "]"

  def postfixString = if (att.isEmpty) "" else (" " + toString())
}
