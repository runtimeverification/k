package org.kframework.kore

import org.kframework.attributes._

import scala.annotation.varargs
import scala.collection.JavaConverters._
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

  def attEquals(other: Any, @varargs attNames: Array[String]): Boolean
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

  def attEquals(other: Any, attNames: Array[String]) = equals(other) && other.asInstanceOf[K].att.attMap.filterKeys(attNames.contains) == att.attMap.filterKeys(attNames.contains)
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

  def computeHashCode = items.hashCode

  def attEquals(that: Any, attNames: Array[String]): Boolean =
    hashCode == that.hashCode && (that match {
      case that: AnyRef if that.asInstanceOf[AnyRef] eq this => true
      case that: KCollection => this.items.asScala.map(new AttCompare(_, attNames:_*)) == that.items.asScala.map(new AttCompare(_, attNames:_*))
      case _ => false
    })
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

  override def computeHashCode = klabel.hashCode * 17 + klist.hashCode

  def attEquals(that: Any, attNames: Array[String]): Boolean =
    hashCode == that.hashCode && (that match {
      case that: AnyRef if that.asInstanceOf[AnyRef] eq this => true
      case that: KApply =>
        that.klabel == klabel && this.klist.attEquals(that.klist, attNames) && att.attMap.filterKeys(attNames.contains) == that.att.attMap.filterKeys(attNames.contains)
      case _ => false
    })
}

trait KSequence extends KCollection with K

trait KVariable extends KItem with KLabel {
  def name: String

  def computeHashCode = name.hashCode

  def attEquals(that: Any, attNames: Array[String]): Boolean = equals(that) && that.asInstanceOf[K].att.attMap.filterKeys(attNames.contains) == att.attMap.filterKeys(attNames.contains)
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

  def attEquals(that: Any, attNames: Array[String]): Boolean =
    hashCode == that.hashCode && (that match {
      case that: AnyRef if that.asInstanceOf[AnyRef] eq this => true
      case that: KRewrite => this.left.attEquals(that.left, attNames) && this.right.attEquals(that.right, attNames) && att.attMap.filterKeys(attNames.contains) == that.att.attMap.filterKeys(attNames.contains)
      case _ => false
    })

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

  def attEquals(that: Any, attNames: Array[String]): Boolean = equals(that) && that.asInstanceOf[K].att.attMap.filterKeys(attNames.contains) == att.attMap.filterKeys(attNames.contains)
}
