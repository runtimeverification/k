package org.kframework.tiny

import org.kframework.kore
import org.kframework.attributes._

trait K extends kore.K {
  var att: Attributes = Attributes()
}

/**
 * Only used in the very special circumstance where there is a match on the KLabel
 */
case class KLabel(name: String) extends kore.KLabel with K

trait KApply extends kore.KApply with K {

  def children: List[K]

  import scala.collection.JavaConverters._

  def klist = kore.ADTConstructors.KList(children.asInstanceOf[List[kore.K]].asJava)
}

case class RegularTerm(klabel: KLabel, children: List[K]) extends KApply