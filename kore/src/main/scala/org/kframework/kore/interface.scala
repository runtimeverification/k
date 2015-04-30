package org.kframework.kore

import org.kframework.attributes._

/**
 * This file contains all inner KORE interfaces.
 * The the wiki for documentation:
 * https://github.com/kframework/k/wiki/KORE-data-structures-guide
 */

trait K extends Serializable {
  def att: Att
  override def toString = Unparse.apply(this)
  def location = att.get("org.kframework.attributes.Location", classOf[Location]).orNull
  def source = att.get("org.kframework.attributes.Source", classOf[Source]).orNull
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
  override def hashCode = sort.hashCode() * 13 + s.hashCode
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
  def stream: java.util.stream.Stream[K] = items.stream()

  override def equals(that: Any): Boolean =
    hashCode == that.hashCode && (that match {
      case that: AnyRef if that.asInstanceOf[AnyRef] eq this => true
      case that: KCollection => this.items == that.items
      case _ => false
    })

  override def hashCode = items.hashCode
}

trait KList extends KCollection {
  def size: Int = items.size
}

trait KApply extends KItem {
  def klabel: KLabel
  def klist: KList
  override def equals(that: Any): Boolean =
    hashCode == that.hashCode && (that match {
      case that: AnyRef if that.asInstanceOf[AnyRef] eq this => true
      case that: KApply =>
        that.klabel == klabel && this.klist == that.klist
      case _ => false
    })

  override def hashCode = klabel.hashCode * 17 + klist.hashCode
}

trait KSequence extends KCollection with K

trait KVariable extends KItem with KLabel {
  def name: String
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

  override def hashCode = left.hashCode * 19 + right.hashCode
}

trait InjectedKLabel extends KItem {
  def klabel: KLabel

  override def equals(that: Any): Boolean =
    hashCode == that.hashCode && (that match {
      case that: AnyRef if that.asInstanceOf[AnyRef] eq this => true
      case that: InjectedKLabel => this.klabel == that.klabel
      case _ => false
    })
}
