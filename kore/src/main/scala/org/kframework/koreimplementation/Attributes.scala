package org.kframework.koreimplementation

import org.kframework._
import scala.collection.mutable.SetBuilder
import scala.collection.mutable.Builder
import org.kframework.builtin.Sorts
import org.kframework.tiny.Pattern
import org.kframework.tiny.Theory
import sun.security.util.Cache.EqualByteArray
import org.kframework.tiny.Or

case class Attributes(att: Set[K] = Set()) extends Collection[K] with Indexed[String, KList] with AttributesToString {
  type This = Attributes

  def contains(label: String): Boolean = (att find {
    case KApply(KLabel(`label`), _, _) => true
    case _ => false
  }) != None

  def get(label: String): Option[KList] = att collect {
    case KApply(KLabel(`label`), l, _) => l
  } headOption

  def getString(label: String): Option[String] = att collect {
    case KApply(KLabel(`label`), KList(KToken(_, l, _)), _) => l
  } headOption

  def getOptionalString(label: String): java.util.Optional[String] =
    getString(label) match {
      case Some(s) => java.util.Optional.of(s);
      case None => java.util.Optional.empty[String]()
    }

  def addAll(that: Attributes) = this ++ that

  def foreach(f: K => Unit): Unit = att foreach f

  def iterable: Iterable[K] = att

  def newBuilder: Builder[K, Attributes] = new SetBuilder[K, Set[K]](Set()) mapResult { new Attributes(_) }

  def +(k: K): Attributes = new Attributes(att + k)
  def +(k: String): Attributes = add(KApply(KLabel(k), KList()))
  def +(kv: (String, String)): Attributes = add(KApply(KLabel(kv._1), KList(KToken(Sorts.KString, kv._2))))

  def ++(that: Attributes) = new Attributes(att ++ that.att)

  // nice methods for Java
  def add(k: K): Attributes = this + k
  def add(k: String): Attributes = this + k
  def add(key: String, value: String): Attributes = this + (key -> value)

  def matchAll(k: K)(implicit disj: Theory): Or = {
    ???
  }

  override def equals(that: Any) = that.isInstanceOf[Attributes]
}

object Attributes {
  def apply(ks: K*) = new Attributes(ks.toSet)

  val classFromUp = "classType"
}

//case class Location(startLine: Int, startColumn: Int, endLine: Int, endColumn: Int) {
//
//  // TODO: Radu: Add offset when the parser knows how to compute it.
//}

object Location {
  import KORE._

  def apply(startLine: Int, startColumn: Int, endLine: Int, endColumn: Int) = {
    'location('startLine(Sorts.Int(startLine.toString)), 'startColumn(Sorts.Int(startColumn.toString)),
      'endLine(Sorts.Int(endLine.toString)), 'endColumn(Sorts.Int(endColumn.toString)))
  }
}

trait AttributesToString {
  self: Attributes =>

  override def toString() =
    "[" +
      (this.filteredAtt map {
        case KApply(KLabel(keyName), KList(KToken(_, value, _)), _) => keyName + "(" + value + ")"
        case x => x.toString
      }).toList.sorted.mkString(" ") +
      "]"

  def postfixString = {
    if (filteredAtt.isEmpty) "" else (" " + toString())
  }

  lazy val filteredAtt: Set[K] = att filter { case KApply(KLabel("productionID"), _, _) => false; case _ => true } // TODO: remove along with KIL to KORE to KIL convertors
}
