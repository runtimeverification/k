package org.kframework.attributes

import org.kframework.builtin.Sorts
import org.kframework.kore._
import org.kframework.kore.{ADTConstructors => cons}
import org.kframework.kore.Unapply._
import collection.JavaConverters._

case class Attributes(att: Set[K]) extends AttributesToString {
  def getK(key: String): Option[K] = att.find {
    case t@KApply(KLabel(`key`), v) => true
  }
  def get[T](key: String): Option[T] = getK(key) map {
    case t: KToken => t.s.asInstanceOf[T]
    case _ => ???
  }

  def getOptional[T](label: String): java.util.Optional[T] =
    get[T](label) match {
      case Some(s) => java.util.Optional.of(s);
      case None => java.util.Optional.empty[T]()
    }

  def contains(label: String): Boolean = (att find {
    case KApply(KLabel(`label`), _) => true
    case _ => false
  }) != None

  def +(k: K): Attributes = new Attributes(att + k)
  def +(k: String): Attributes = add(cons.KApply(cons.KLabel(k), cons.KList(), Attributes()))
  def +(kv: (String, String)): Attributes = add(cons.KApply(cons.KLabel(kv._1), cons.KList(cons.KToken(Sorts.KString, kv._2, Attributes())), Attributes()))
  def ++(that: Attributes) = new Attributes(att ++ that.att)

  // nice methods for Java
  def add(k: K): Attributes = this + k
  def add(k: String): Attributes = this + k
  def add(key: String, value: String): Attributes = this + (key -> value)

  def stream = att.asJava.stream
  def addAll(that: Attributes) = this ++ that
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