package org.kframework.tiny

import org.kframework._
import org.kframework.attributes.Att
import org.kframework.kore.ADT

import scala.collection.JavaConverters._
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.reflect.ClassTag

// Traits

trait K extends kore.K {
  def att: Att
  def matcher(right: K): Matcher = ???
}

object KApp {
  def unapply(k: KApp): Option[(Label, Seq[K], Att)] = Some(k.klabel, k.children.toSeq, k.att)
}

/**
 * Term with children. We automatically lift KSeq and KRewrite to KApp.
 */
trait KApp extends kore.KApply with K {
  // KApp seen as a collection Set(2, Set(3, 4)) is normalized and has size 3 and 2,3,4 as children
  def size: Int = children.size
  def children: Iterable[K]

  def klabel: Label
  // The KApp seen as a KApply -- Set(2, Set(3, 4)) is normalized, but klist = KList(2, Set(3, 4))
  def klist = kore.ADTConstructors.KList(children.asInstanceOf[List[kore.K]].asJava)

  override def equals(that: Any) = {
    (that match {
      case that: KApp => that.klabel == klabel && this.children == that.children
      case _ => false
    })
  }
}

/**
 * Term without children.
 */
trait KLeaf extends K {
  def copy(att: Att): KLeaf
}

/**
 * KApp with a collection of children which are usually defined using an associative operator.
 */
trait KCollection extends KApp {
  def klabel: KCollectionLabel

  def head: K = children.head
  def tail: KCollection = klabel.construct(children.tail, att)
  def map(f: K => K): KCollection = klabel.construct(children.map(f), att)
}

/**
 * KApp with fixed arity. It is defined using a non-associative operator.
 */
trait KProduct extends KApp with Product {
  val children = productIterator collect { case k: K => k } toIterable
}

/**
 * KToken-like term, i.e. term without children representing a constant value.
 * KSimpleTok is one example. KInt is another.
 */
trait KTok extends kore.KToken with KLeaf

// Classes

case class KVar(name: String, att: Att = Att()) extends kore.KVariable with KLeaf {
  def copy(att: Att): KVar = KVar(name, att)
}

case class RegularKTok(sort: Sort, s: String, att: Att = Att()) extends KTok {
  def copy(att: Att): RegularKTok = RegularKTok(sort, s, att)
}

class RegularKApp(val klabel: RegularKAppLabel, val children: Seq[K], val att: Att = Att()) extends KApp

class AssocKApp(val klabel: AssocKAppLabel, val children: Seq[K], val att: Att = Att()) extends KCollection

class KSeq private(val children: Seq[K], val att: Att) extends kore.KSequence with K with KCollection {
  def klabel = KSeq
  def items: java.util.List[kore.K] = children.toList.asInstanceOf[List[kore.K]].asJava
}

case class KRewrite(val left: K, val right: K, val att: Att) extends kore.KRewrite with KProduct {
  def klabel = KRewrite
}

case class InjectedLabel(klabel: Label, att: Att) extends kore.InjectedKLabel with KTok {
  override def copy(att: Att): KLeaf = InjectedLabel(klabel, att)
  val sort: Sort = InjectedLabel.sort
  val s: String = klabel.toString
}

object InjectedLabel {
  val sort = ADT.Sort("InjectedKLabel")
}

// Label traits

trait Label extends kore.KLabel {
  def apply(l: Seq[K], att: Att)(implicit t: Theory): K =
    t.normalize(construct(l, att))

  def construct(l: Iterable[K], att: Att): KApp
  def apply(l: K*)(implicit t: Theory): K = apply(l, Att())
  def att: Att
}


trait KCollectionLabel extends Label {
  def construct(l: Iterable[K], att: Att): KCollection
}

// Labels

object KRewrite extends Label {
  val att = Att()
  val name = "=>"
  def construct(l: Iterable[K], att: Att): KRewrite =
    l match {
      case List(left, right) => new KRewrite(left, right, att)
    }
}

case class RegularKAppLabel(name: String, att: Att) extends Label {
  override def construct(l: Iterable[K], att: Att): RegularKApp = new RegularKApp(this, l.toSeq, att)
}

trait AssocKAppLabel extends KCollectionLabel {
  def construct(l: Iterable[K], att: Att): KCollection = {
    val b = newBuilder(att)
    l foreach b.+=
    b.result()
  }
  def newBuilder[AssocIn <: {def iterator : Iterator[K]} : ClassTag](att: Att): mutable.Builder[K, KCollection] =
    new AssocBuilder[K, List[K], AssocIn](ListBuffer()).mapResult { constructFromFlattened(_, att) }
  def constructFromFlattened(l: Seq[K], att: Att): KCollection
}

object AssocKAppLabel {
  def apply(nameP: String, attP: Att) = new AssocKAppLabel {
    val name = nameP;
    val att = attP
    override def constructFromFlattened(l: Seq[K], att: Att): KCollection = new AssocKApp(this, l, att)
  }
}

object KSeq extends {
  val name = "~>";
  val att = Att()
} with AssocKAppLabel {
  /* required */
  override def constructFromFlattened(l: Seq[K], att: Att): KCollection = new KSeq(l, att)
}
