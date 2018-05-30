package org.kframework.kore

import org.kframework.attributes._
import org.kframework.kore.ADT.{KApply, KList}
import org.kframework.unparser.ToKast

/**
 * This file contains all inner KORE interfaces.
 * The the wiki for documentation:
 * https://github.com/kframework/k/wiki/KORE-data-structures-guide
 */

trait K extends Serializable {
  def att: Att
  override def toString = ToKast.apply(this)

  lazy val cachedHashCode = computeHashCode

  override def hashCode = cachedHashCode

  def computeHashCode: Int
}

trait KItem extends K

trait KLabel {
  def name: String
  def params: Seq[Sort]
  override def equals(other: Any) = other match {
    case l: KLabel => name == l.name && params == l.params
    case _ => false
  }
  override def hashCode = name.hashCode * 29 + params.hashCode

  def apply(ks: K*) = KApply(this, KList(ks.toList))
}

trait KToken extends KItem {
  def sort: Sort
  def s: String
  override def equals(other: Any) = other match {
    case other: KToken => sort == other.sort && s == other.s
    case _ => false
  }
  def computeHashCode = sort.hashCode() * 13 + s.hashCode
}

trait Sort {
  def name: String
  def params: Seq[Sort]
  override def equals(other: Any) = other match {
    case other: Sort => name == other.name && params == other.params
    case _ => false
  }
  override def hashCode = name.hashCode * 23 + params.hashCode
}

trait KCollection {
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

  def computeHashCode = items.hashCode
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

trait KVariable extends KItem with KLabel {
  def name: String

  def computeHashCode = name.hashCode
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

  def computeHashCode = pattern.hashCode * 19 + alias.hashCode
}

trait KRewrite extends K {
  def left: K
  def right: K

  override def equals(that: Any): Boolean =
    hashCode == that.hashCode && (that match {
      case that: AnyRef if that.asInstanceOf[AnyRef] eq this => true
      case that: KRewrite => this.left == that.left && this.right == that.right
      case _ => false
    })

  def computeHashCode = left.hashCode * 19 + right.hashCode
}

trait InjectedKLabel extends KItem {
  def klabel: KLabel

  override def equals(that: Any): Boolean =
    hashCode == that.hashCode && (that match {
      case that: AnyRef if that.asInstanceOf[AnyRef] eq this => true
      case that: InjectedKLabel => this.klabel == that.klabel
      case _ => false
    })

  def computeHashCode = klabel.hashCode
}
