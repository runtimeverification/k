package org.kframework.tiny

import org.kframework._
import org.kframework.attributes.Att
import org.kframework.kore.ADT

import scala.collection.JavaConverters._
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

//////////////////
//   TRAITS
//////////////////

trait K extends kore.K {
  def att: Att
  def matcher(right: K): Matcher
  def normalize(implicit theory: Theory): K
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

  val klabel: Label
  // The KApp seen as a KApply -- Set(2, Set(3, 4)) is normalized, but klist = KList(2, Set(3, 4))
  def klist = kore.ADTConstructors.KList(children.asInstanceOf[Iterable[kore.K]].toSeq.asJava)

  override def equals(that: Any) = {
    (that match {
      case that: KApp => that.klabel == klabel && this.children == that.children
      case _ => false
    })
  }

  def normalize(implicit theory: Theory): K =
    klabel((children map theory.normalize).toSeq, att)

  override def toString = klabel + "(" + children.mkString(",") + ")"
}

/**
 * Term without children.
 */
trait KLeaf extends K {
  def copy(att: Att): KLeaf
  def normalize(implicit theory: Theory): K = theory.normalize(this)
}

/**
 * KApp with a collection of children which are usually defined using an associative operator.
 */
trait KAssocApp extends KApp {
  val klabel: KAssocAppLabel

  def head: K = children.head
  def tail: KAssocApp = klabel.construct(children.tail, att)
  def map(f: K => K): KAssocApp = klabel.construct(children.map(f), att)

  override def matcher(right: K): Matcher = ???
}

trait KRegularApp extends KApp {
  val klabel: KRegularAppLabel
  override def matcher(other: K) = KRegularAppMatcher(this, other)
}

/**
 * KApp with fixed arity. It is defined using a non-associative operator.
 */
trait KProduct extends KRegularApp with Product {
  val children = productIterator collect { case k: K => k } toIterable
}

/**
 * KToken-like term, i.e. term without children representing a constant value.
 * KSimpleTok is one example. KInt is another.
 */
trait KTok extends kore.KToken with KLeaf {
  override def matcher(right: K): Matcher = EqualsMatcher(this, right)
}

trait EmptyAtt {
  def att = Att()
}

///////////////////
//   CLASSES
///////////////////

case class KVar(name: String, att: Att = Att()) extends kore.KVariable with KLeaf {
  def copy(att: Att): KVar = KVar(name, att)
  override def matcher(right: K): Matcher = KVarMatcher(this, right)
  override def toString = name
}

case class RegularKTok(sort: Sort, s: String, att: Att = Att()) extends KTok {
  def copy(att: Att): RegularKTok = RegularKTok(sort, s, att)
  override def toString = s + ":" + sort
}

class RegularKApp(val klabel: RegularKAppLabel, val children: Seq[K], val att: Att = Att()) extends KRegularApp

class RegularKAssocApp(val klabel: KAssocAppLabel, val children: Seq[K], val att: Att = Att()) extends KAssocApp

class KSeq private(val children: Seq[K], val att: Att) extends kore.KSequence with K with KAssocApp {
  val klabel = KSeq
  def items: java.util.List[kore.K] = children.toList.asInstanceOf[List[kore.K]].asJava
}

case class KRewrite(val left: K, val right: K, val att: Att) extends kore.KRewrite with KProduct {
  val klabel = KRewrite
}

case class InjectedLabel(klabel: Label, att: Att) extends kore.InjectedKLabel with KTok {
  override def copy(att: Att): KLeaf = InjectedLabel(klabel, att)
  val sort: Sort = InjectedLabel.sort
  val s: String = klabel.toString
}

object InjectedLabel {
  val sort = ADT.Sort("InjectedKLabel")
}

/////////////////////
//   LABEL TRAITS
/////////////////////

trait Label extends kore.KLabel {
  def apply(l: Seq[K], att: Att): K =
    construct(l, att)

  def construct(l: Iterable[K], att: Att): KApp
  def apply(l: K*): K = apply(l, Att())
  def att: Att

  override def toString = name
}

trait KRegularAppLabel extends Label {

}

trait KProduct1Label extends KRegularAppLabel {
  def apply(k: K, att: Att): KProduct
  def construct(l: Iterable[K], att: Att): KProduct =
    l match {case List(k) => apply(k, att) }
}

trait KProduct2Label extends KRegularAppLabel {
  def apply(k1: K, k2: K, att: Att): KProduct
  def construct(l: Iterable[K], att: Att): KProduct =
    l match {case Seq(k1, k2) => apply(k1, k2, att) }
}

trait KAssocAppLabel extends Label {
  def construct(l: Iterable[K], att: Att): KAssocApp = {
    val b = newBuilder(att)
    l foreach b.+=
    b.result()
  }
  def newBuilder(att: Att): mutable.Builder[K, KAssocApp] =
    new KAppAssocBuilder(ListBuffer[K](), this).mapResult { constructFromFlattened(_, att) }
  def constructFromFlattened(l: Seq[K], att: Att): KAssocApp
}


///////////////
//   LABELS
///////////////

object KRewrite extends KRegularAppLabel {
  val att = Att()
  val name = "=>"
  def construct(l: Iterable[K], att: Att): KRewrite =
    l match {
      case List(left, right) => new KRewrite(left, right, att)
    }
}

case class RegularKAppLabel(name: String, att: Att) extends KRegularAppLabel {
  override def construct(l: Iterable[K], att: Att): RegularKApp = new RegularKApp(this, l.toSeq, att)
}

case class RegularKAssocAppLabel(name: String, att: Att) extends KAssocAppLabel {
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new RegularKAssocApp(this, l, att)
}

object KSeq extends {
  val name = "~>";
  val att = Att()
} with KAssocAppLabel {
  /* required */
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new KSeq(l, att)
}
