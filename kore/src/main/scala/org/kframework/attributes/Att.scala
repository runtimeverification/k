package org.kframework.attributes

import org.kframework.builtin.Sorts
import org.kframework.kore._
import org.kframework.kore.{ADTConstructors => cons}
import org.kframework.kore.Unapply._
import collection.JavaConverters._

case class Att(att: Set[K]) extends AttributesToString {
  def getK(key: String): Option[K] = att.find {
    case t@KApply(KLabel(`key`), v) => true
    case _ => false
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

  def contains(label: String): Boolean =
    att exists {
      case KApply(KLabel(`label`), _) => true
      case z => false
    }

  def +(k: K): Att = new Att(att + k)
  def +(k: String): Att = add(cons.KApply(cons.KLabel(k), cons.KList(), Att()))
  def +(kv: (String, String)): Att = add(cons.KApply(cons.KLabel(kv._1), cons.KList(cons.KToken(Sorts.KString, kv._2, Att())), Att()))
  def ++(that: Att) = new Att(att ++ that.att)

  // nice methods for Java
  def add(k: K): Att = this + k
  def add(k: String): Att = this + k
  def add(key: String, value: String): Att = this + (key -> value)

  def stream = att.asJava.stream
  def addAll(that: Att) = this ++ that
}

trait KeyWithType

object Att {
  def apply(atts: K*): Att = Att(atts.toSet)
}

trait AttributesToString {
  self: Att =>

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