package org.kframework.kore

import java.util.Optional

import org.kframework.attributes._
import org.kframework.kore.ADT.{KApply, KList}
import org.kframework.unparser.ToKast
import org.kframework.HasCachedHashCode

import scala.collection.JavaConverters._

/**
 * This file contains all inner KORE interfaces.
 * The the wiki for documentation:
 * https://github.com/kframework/k/wiki/KORE-data-structures-guide
 */

trait K extends Serializable with HasLocation with HasCachedHashCode {
  def att: Att
  override def toString = ToKast.apply(this)
  def location: Optional[Location] = att.getOptional(classOf[Location])
  def source: Optional[Source] = att.getOptional(classOf[Source])
}

object K {
  implicit val ord = new Ordering[K] {
    def compare(a: K, b: K): Int = {
      import scala.math.Ordering.Implicits._
      (a, b) match {
        case (c: KToken, d: KToken) => Ordering.Tuple2(Ordering[String], Ordering[Sort]).compare((c.s, c.sort), (d.s, d.sort))
        case (c: KApply, d: KApply) => Ordering.Tuple2(KLabelOrdering, seqDerivedOrdering[Seq, K](this)).compare((c.klabel, c.klist.items.asScala), (d.klabel, d.klist.items.asScala))
        case (c: KSequence, d: KSequence) => seqDerivedOrdering(this).compare(c.items.asScala, d.items.asScala)
        case (c: KVariable, d: KVariable) => Ordering[String].compare(c.name, d.name)
        case (c: KAs, d: KAs) => Ordering.Tuple2(this, this).compare((c.pattern, c.alias), (d.pattern, d.alias))
        case (c: KRewrite, d: KRewrite) => Ordering.Tuple2(this, this).compare((c.left, c.right), (d.left, d.right))
        case (c: InjectedKLabel, d: InjectedKLabel) => KLabelOrdering.compare(c.klabel, d.klabel)
        case (_:KToken, _) => 1
        case (_, _:KToken) => -1
        case (_:KApply, _) => 1
        case (_, _:KApply) => -1
        case (_:KSequence, _) => 1
        case (_, _:KSequence) => -1
        case (_:KVariable, _) => 1
        case (_, _:KVariable) => -1
        case (_:KAs, _) => 1
        case (_, _:KAs) => -1
        case (_:KRewrite, _) => 1
        case (_, _:KRewrite) => -1
        case (_:InjectedKLabel, _) => 1
        case (_, _:InjectedKLabel) => -1
      }
    }
  }
}

trait KItem extends K

trait KLabel extends HasCachedHashCode {
  def name: String
  def params: Seq[Sort]
  override def equals(other: Any) = other match {
    case l: KLabel => name == l.name && params == l.params
    case _ => false
  }
  override def computeHashCode = name.hashCode * 29 + params.hashCode

  def apply(ks: K*) = KApply(this, KList(ks.toList))   
}

object KLabelOrdering extends Ordering[KLabel] {
  def compare(a: KLabel, b: KLabel): Int = {
    import scala.math.Ordering.Implicits._
    Ordering.Tuple2(Ordering[String], seqDerivedOrdering[Seq, Sort](Ordering[Sort])).compare((a.name, a.params), (b.name, b.params))
  }
}

trait KToken extends KItem {
  def sort: Sort
  def s: String
  override def equals(other: Any) = other match {
    case other: KToken => sort == other.sort && s == other.s
    case _ => false
  }
  override def computeHashCode = sort.hashCode() * 13 + s.hashCode
}

trait Sort extends Ordered[Sort] with HasCachedHashCode {
  def name: String
  def params: Seq[Sort]
  override def equals(other: Any) = other match {
    case other: Sort => name == other.name && params == other.params
    case _ => false
  }
  override def computeHashCode = name.hashCode * 23 + params.hashCode
    
  def compare(that: Sort): Int = {
    import scala.math.Ordering.Implicits._
    Ordering.Tuple2(Ordering[String], seqDerivedOrdering[Seq, Sort](Ordering.ordered(identity))).compare((this.name, this.params), (this.name, this.params))
  }
}

trait KCollection extends HasCachedHashCode {
  def items: java.util.List[K]
  def size: Int
  def asIterable: java.lang.Iterable[_ <: K]
  def stream: java.util.stream.Stream[K] = items.stream()

  override def equals(that: Any): Boolean =
    hashCode == that.hashCode && (that match {
      case that: AnyRef if that.asInstanceOf[AnyRef] eq this => true
      case that: KCollection => this.items == that.items
      case _ => false
    })

  override def computeHashCode = items.hashCode
}

trait KList extends KCollection {
}

trait KApply extends KItem with KCollection {
  def klabel: KLabel
  def klist: KList

  override def equals(that: Any): Boolean =
    hashCode == that.hashCode && (that match {
      case that: AnyRef if that.asInstanceOf[AnyRef] eq this => true
      case that: KApply =>
        that.klabel == klabel && this.klist == that.klist
      case _ => false
    })

  override def computeHashCode = klabel.hashCode * 17 + klist.hashCode
}

trait KSequence extends KCollection with K

trait KVariable extends KItem with KLabel with org.kframework.Equals[KVariable] {
  def name: String

  override def computeHashCode = name.hashCode

  override def typedEquals(other : KVariable) =
    name == other.name
}

trait KAs extends K {
  def pattern: K
  def alias: K

  override def equals(that: Any): Boolean =
    hashCode == that.hashCode && (that match {
      case that: AnyRef if that.asInstanceOf[AnyRef] eq this => true
      case that: KAs => this.pattern == that.pattern && this.alias == that.alias
      case _ => false
    })

  override def computeHashCode = pattern.hashCode * 19 + alias.hashCode
}

trait KRewrite extends K with org.kframework.Equals[KRewrite] {
  def left: K
  def right: K

  override def equals(that: Any): Boolean =
    hashCode == that.hashCode && super.equals(that)

  override def typedEquals(that : KRewrite) = 
    left == that.left && right == that.right

  override def computeHashCode = left.hashCode * 19 + right.hashCode
}

trait InjectedKLabel extends KItem {
  def klabel: KLabel

  override def equals(that: Any): Boolean =
    hashCode == that.hashCode && (that match {
      case that: AnyRef if that.asInstanceOf[AnyRef] eq this => true
      case that: InjectedKLabel => this.klabel == that.klabel
      case _ => false
    })

  override def computeHashCode = klabel.hashCode
}
