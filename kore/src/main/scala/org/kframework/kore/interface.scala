package org.kframework.kore

trait K

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

trait KList {
  def items: java.lang.Iterable[K]
}

trait KApply extends KItem {
  def klabel: KLabel
  def klist: KList
}

trait KSequence extends K {
  def left: K
  def right: K
}

trait KVariable extends KItem with KLabel {
  def name: String
}

trait KRewrite extends K {
  def left: K
  def right: K
}
