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
  def canEqual(that: Any) = that match {
    case that: K => label == that.label && att == that.att
    case _ => false
  }
  def matcher(right: K): Matcher = ???
}

object KApp {
  def unapply(k: KApp): Option[(Label[_ <: K], Seq[K], Att)] = Some(k.klabel, k.children.toSeq, k.att)
}

trait KApp extends K {
  def size: Int
  def children: Iterable[K]
  def items: java.util.List[kore.K] = children.toList.asInstanceOf[List[kore.K]].asJava
  def klist = kore.ADTConstructors.KList(children.asInstanceOf[List[kore.K]].asJava)
  val klabel = label
}

trait KCollection extends kore.KCollection with KApp with Collection[K] {
  type This <: KCollection
  override def size = super[Collection].size
  def iterable: Iterable[K] = children
  def label: KCollectionLabel[This]
  def newBuilder(): mutable.Builder[K, This] = label.newBuilder(att)
}

trait ProductOfKs extends KApp with Product {
  type This <: ProductOfKs
  val children = productIterator collect { case k: K => k } toIterable
  val size = productArity
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

class RegularKApp(val label: RegularKAppLabel, val children: Seq[K], val att: Att = Att()) extends KCollection {
  type This = RegularKApp
}

class AssocKApp(val label: AssocKAppLabel, val children: Seq[K], val att: Att = Att()) extends KCollection {
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

case class InjectedLabel(klabel: Label[_ <: K], att: Att) extends kore.InjectedKLabel with K {
  val label = klabel
}

// Label traits

trait Label[+This <: K] extends kore.KLabel {
  def apply(l: Seq[K], att: Att)(implicit t: Theory): K =
    t.normalize(construct(l, att))

  def construct(l: Seq[K], att: Att): This
  def apply(l: K*)(implicit t: Theory): K = apply(l, Att())
  def att: Att
}

trait KCollectionLabel[This <: K] extends Label[This] {
  def newBuilder(att: Att): mutable.Builder[K, This]
  def construct(l: Seq[K], att: Att): This = {
    val b = newBuilder(att)
    l foreach b.+=
    b.result()
  }
}

trait SelfLabel[Self <: K] extends Label[Self] {
  self: K =>
  type This = Self
  def label = this
  def copy(att: Att): This
  def construct(l: Seq[K], att: Att) = { assert(l.size == 0); copy(att) }
}

// Labels

object KRewrite extends Label[KRewrite] {
  val att = Att()
  val name = "=>"
  def construct(l: Seq[K], att: Att): KRewrite =
    l match {
      case List(left, right) => new KRewrite(left, right, att)
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

object KSeq extends {
  val name = "~>";
  val att = Att()
} with KCollectionLabel[KSeq] {
  /* required */
  def newBuilder(att: Att): mutable.Builder[K, KSeq] = new AssocBuilder[K, List[K], KSeq](ListBuffer()).mapResult {
    new KSeq(_, att)
  }
}
