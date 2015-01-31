package org.kframework.tiny

import org.kframework.{kore, _}

import scala.collection.JavaConverters._
import org.kframework.attributes.Attributes

trait K extends kore.K

/**
 * Only used in the very special circumstance where there is a match on the KLabel
 */
case class KLabel(name: String) extends kore.KLabel

trait KCollection extends kore.KCollection with Collection[K] {
  override def size = super[Collection].size
}

trait KApply extends kore.KApply with KCollection {
  def children: List[K]
  def klist = kore.ADTConstructors.KList(children.asInstanceOf[List[kore.K]].asJava)
  override val size = super[KCollection].size
  override def stream = super[KCollection].stream
}

case class KVariable(name: String, att: Attributes = Attributes()) extends kore.KVariable
