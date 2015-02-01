package org.kframework.kore

import org.kframework.attributes._

trait K {
  def att: Att
}

trait KItem extends K

trait KLabel {
  def name: String
  override def equals(other: Any) = other match {
    case l: KLabel => name == l.name
    case _ => false
  }
}

trait KToken extends KItem {
  def sort: Sort
  def s: String
  override def equals(other: Any) = other match {
    case other: KToken => sort == other.sort && s == other.s
    case _ => false
  }
}

trait Sort {
  def name: String
  override def equals(other: Any) = other match {
    case other: Sort => name == other.name
    case _ => false
  }
}

trait KCollection {
  def items: java.util.List[K]
  def stream: java.util.stream.Stream[K] = items.stream()
  def size = items.size
}

trait KList extends KCollection

trait KApply extends KItem {
  def klabel: KLabel
  def klist: KList
}

trait KSequence extends KCollection

trait KVariable extends KItem with KLabel {
  def name: String
}

trait KRewrite extends K {
  def left: K
  def right: K
}

trait InjectedKLabel extends KItem {
  def klabel: KLabel
}
