package org.kframework.tiny

import org.kframework._
import org.kframework.attributes.Att

import scala.collection.JavaConverters._
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

// Traits

trait K extends kore.K {
  type This <: K

  def label: Label[This]
  def att: Att
  def copy(att: Att): This
  def canEqual(that: Any) = that match {
    case that: K => label == that.label && att == that.att
    case _ => false
  }
}

trait KCollection extends kore.KCollection with Collection[K] with K {
  type This <: KCollection
  override def size = super[Collection].size
  def copy(att: Att) = label.apply(iterable.toSeq, att)
  def iterable: Iterable[K] = children
  def children: Iterable[K]
  def label: KCollectionLabel[This]
  def newBuilder(): mutable.Builder[K, This] = label.newBuilder(att)
  def items: java.util.List[kore.K] = iterable.toList.asInstanceOf[List[kore.K]].asJava
}

trait KApp extends kore.KApply with KCollection {
  def children: Seq[K]
  def klist = kore.ADTConstructors.KList(children.asInstanceOf[List[kore.K]].asJava)
  val klabel = label
}

trait ProductOfKs extends KCollection with Product {
  type This <: ProductOfKs
  val children = productIterator collect { case k: K => k } toIterable
}

// Classes

case class KVar(name: String, att: Att = Att()) extends kore.KVariable with K with SelfLabel[KVar] {
  override type This = KVar
  override def copy(att: Att): This = KVar(name, att)
}

case class KTok(sort: Sort, s: String, att: Att = Att()) extends kore.KToken with K with SelfLabel[KTok] {
  override type This = KTok
  def name: String = s + ":" + sort
  def copy(att: Att): This = KTok(sort, s, att)
}

class RegularKApp(val label: RegularKAppLabel, val children: Seq[K], val att: Att = Att()) extends KApp {
  type This = RegularKApp
}

class AssocKApp(val label: AssocKAppLabel, val children: Seq[K], val att: Att = Att()) extends KApp {
  type This = AssocKApp
}

class KSeq private(val children: Seq[K], val att: Att) extends kore.KSequence with K with KCollection {
  type This = KSeq
  def label = KSeq
}

case class KRewrite(val left: K, val right: K, val att: Att) extends kore.KRewrite with ProductOfKs {
  type This = KRewrite
  def label = KRewrite
}

case class InjectedLabel(klabel: Label[_ <: K], att: Att) extends kore.InjectedKLabel

// Label traits

trait Label[+This <: K] extends kore.KLabel {
  def apply(l: Seq[K], att: Att): This
  def apply(l: K*): This = apply(l, Att())
  def att: Att
}

trait KCollectionLabel[This <: K] extends Label[This] {
  def newBuilder(att: Att): mutable.Builder[K, This]
  def apply(l: Seq[K], att: Att): This = {
    val b = newBuilder(att)
    l foreach b.+=
    b.result()
  }
}

trait SelfLabel[Self <: K] extends Label[Self] {
  self: K =>
  type This = Self
  def label = this
  def apply(l: Seq[K], att: Att) = { assert(l.size == 0); copy(att) }
}

// Labels

object KRewrite extends KCollectionLabel[KRewrite] {
  def newBuilder(att: Att): mutable.Builder[K, KRewrite] =
    ListBuffer() mapResult { case List(left, right) => new KRewrite(left, right, att) }
  val att = Att()
  val name = "=>"
}

case class RegularKAppLabel(name: String, att: Att) extends KCollectionLabel[RegularKApp] {
  def newBuilder(att: Att): mutable.Builder[K, RegularKApp] =
    ListBuffer() mapResult { new RegularKApp(this, _, att) }
}

case class AssocKAppLabel(name: String, att: Att) extends KCollectionLabel[AssocKApp] {
  def newBuilder(att: Att): mutable.Builder[K, AssocKApp] =
    new AssocBuilder[K, List[K], KSeq](ListBuffer()).mapResult { new AssocKApp(this, _, att) }
}

object KSeq extends {
  val name = "~>";
  val att = Att()
} with KCollectionLabel[KSeq] {
  /* required */
  def newBuilder(att: Att): mutable.Builder[K, KSeq] = new AssocBuilder[K, List[K], KSeq](ListBuffer()).mapResult {
    new KSeq(_, att)
  }
}
