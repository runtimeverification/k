package org.kframework.attributes

import org.kframework.Collections._
import org.kframework.builtin.Sorts
import org.kframework.kore.Unapply._
import org.kframework.kore.{K, KORE}
import org.kframework.meta.Down

import scala.collection.JavaConverters._

case class Att(att: Set[K]) extends AttributesToString {
  def getK(key: String): Option[K] = {
    att.collectFirst({
      case t@KApply(KLabel(`key`), List(v)) => v
    })
  }

  val down = Down(Set("scala.collection.immutable"))

  def get[T](key: String): Option[T] = getK(key) map down map { _.asInstanceOf[T] }

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
  def +(k: String): Att = add(KORE.KApply(KORE.KLabel(k), KORE.KList(), Att()))
  def +(kv: (String, String)): Att = add(KORE.KApply(KORE.KLabel(kv._1), KORE.KList(KORE.KToken(Sorts.KString, kv._2,
    Att())), Att()))
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
  @annotation.varargs def apply(atts: K*): Att = Att(atts.toSet)

  implicit def asK(key: String, value: String) =
    KORE.KApply(KORE.KLabel(key), KORE.KList(mutable(List(KORE.KToken(Sorts.KString, value, Att())))), Att())
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

  lazy val filteredAtt: List[K] =
    (att filter { case KApply(KLabel("productionID"), _) => false; case _ => true }).toList sortBy { _.toString }
  // TODO: remove along with KIL to KORE to KIL convertors
}
