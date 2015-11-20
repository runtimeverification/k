package org.kframework.kore

import org.kframework.attributes._
import org.kframework.unparser.Unparse

/**
 * This file contains all inner KORE interfaces.
 * The the wiki for documentation:
 * https://github.com/kframework/k/wiki/KORE-data-structures-guide
 */

trait K extends Serializable {
  def att: Att
  override def toString = Unparse.apply(this)

  lazy val cachedHashCode = computeHashCode

  override def hashCode = cachedHashCode

  def computeHashCode: Int
}

trait KItem extends K

trait KLabel {
  def name: String
  override def equals(other: Any) = other match {
    case l: KLabel => name == l.name
    case _ => false
  }
  override def hashCode = name.hashCode
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
  override def equals(other: Any) = other match {
    case other: Sort => name == other.name
    case _ => false
  }
  override def hashCode = name.hashCode
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
