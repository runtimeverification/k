package org.kframework.tiny

import org.kframework.kore
import org.kframework.attributes._
import scala.collection.JavaConverters._

trait K extends kore.K

/**
 * Only used in the very special circumstance where there is a match on the KLabel
 */
case class KLabel(name: String) extends kore.KLabel

trait KCollection extends kore.KCollection {
  val items: java.util.List[kore.K]
}

trait KApply extends kore.KApply with K {
  def children: List[K]
  def klist = kore.ADTConstructors.KList(children.asInstanceOf[List[kore.K]].asJava)
}

case class RegularTerm(klabel: KLabel, children: List[K], att: Attributes) extends KApply