package org.kframework.kore

import org.kframework.kore
import org.kframework.attributes._

trait K {
  def att: Attributes
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

// objects for unapply -- we keep them in the same file as Scala requires this

object KLabel {
  def unapply(klabel: KLabel) = Some(klabel.name)
}

object KToken {
  def unapply(token: KToken) = Some(token.sort, token.s)
}

object Sort {
  def unapply(sort: Sort) = Some(sort.name)
}

object KApply {

  import collection.JavaConverters._

  def unapply(kapply: KApply) = Some(kapply.klabel, kapply.klist.items.asScala.toList)
}

object KSequence {
  def unapply(kseq: KSequence) = Some(kseq.left, kseq.right)
}

object KList {

  import scala.collection.JavaConverters._

  def unapplySeq(klist: KList): Option[Seq[kore.K]] = Some(klist.items.asScala.toSeq)
}