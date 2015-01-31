package org.kframework.kore

import org.kframework.attributes._

trait K {
  def att: Att
}

trait KItem extends K

trait KLabel {
  def name: String
}

trait KToken extends KItem {
  def sort: Sort
  def s: String
}

trait Sort {
  def name: String
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

  def items = klist.items
  def stream: java.util.stream.Stream[K] = klist.stream
  def size = items.size
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
