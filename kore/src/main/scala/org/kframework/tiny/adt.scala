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
  override def iterable: Iterable[K] = children
  def children: Iterable[K]
  def label: KCollectionLabel[This]
  override def newBuilder(): mutable.Builder[K, This] = label.newBuilder(att)
  override def items: java.util.List[kore.K] = iterable.toList.asInstanceOf[List[kore.K]].asJava
}

trait KApp extends kore.KApply with KCollection {
  def children: Seq[K]
  def klist = kore.ADTConstructors.KList(children.asInstanceOf[List[kore.K]].asJava)
  override val size = super[KCollection].size
  override def stream = super[KCollection].stream
  val klabel = label
}

// Classes

case class KVar(name: String, att: Att = Att()) extends kore.KVariable

case class KTok(sort: Sort, s: String, att: Att = Att()) extends kore.KToken with K with Label[KTok] {
  override type This = KTok
  override def label: Label[KTok] = this
  override def name: String = s + ":" + sort
  def apply(l: Seq[K], att: Att): This = { assert(l.size == 0); KTok(sort, s, att) }
  override def copy(att: Att): This = KTok(sort, s, att)
}

class RegularKApp(val label: RegularKAppLabel, val children: Seq[K], val att: Att = Att()) extends KApp {
  override type This = RegularKApp
}

class AssocKApp(val label: AssocKAppLabel, val children: Seq[K], val att: Att = Att()) extends KApp {
  override type This = AssocKApp
}

class KSeq private(val children: Seq[K], val att: Att) extends kore.KSequence with K with KCollection {
  override type This = KSeq
  override def label: KSeq.type = KSeq
}

// Labels

trait Label[+This <: K] extends kore.KLabel {
  def apply(l: Seq[K], att: Att): This
  def att: Att
}

//trait CompanionLabel extends Label {
//  def name = this.getClass.getCanonicalName
//  def att = Att()
//}

trait KCollectionLabel[This <: K] extends Label[This] {
  def newBuilder(att: Att): mutable.Builder[K, This]
  def apply(l: Seq[K], att: Att): This = {
    val b = newBuilder(att)
    l foreach b.+=
    b.result()
  }
}

case class RegularKAppLabel(name: String, att: Att) extends KCollectionLabel[RegularKApp] {
  def newBuilder(att: Att): mutable.Builder[K, RegularKApp] =
    ListBuffer() mapResult { new RegularKApp(this, _, att) }
}

case class AssocKAppLabel(name: String, att: Att) extends KCollectionLabel[AssocKApp] {
  def newBuilder(att: Att): mutable.Builder[K, AssocKApp] =
    new AssocBuilder[K, List[K], KSeq](ListBuffer()).mapResult { new AssocKApp(this, _, att) }
}

object KSeq extends KCollectionLabel[KSeq] {
  override def att: Att = Att()
  override def name: String = "~>"
  def newBuilder(att: Att): mutable.Builder[K, KSeq] = new AssocBuilder[K, List[K], KSeq](ListBuffer()).mapResult { new KSeq(_, att) }
}
