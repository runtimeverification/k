package org.kframework.kore

import org.kframework.kore
import org.kframework.attributes._
import collection.JavaConverters._

object ADT {

  case class KLabel(name: String) extends kore.KLabel

  case class KApply[KK <: K](klabel: kore.KLabel, klist: kore.KList, att: Attributes = Attributes()) extends kore.KApply

  case class KSequence(elements: List[K], att: Attributes = Attributes()) extends kore.KSequence {
    def items: java.util.List[K] = elements.asJava
  }

  case class KVariable(name: String, att: Attributes = Attributes()) extends kore.KVariable

  case class Sort(name: String) extends kore.Sort {
    override def toString = name
  }

  case class KToken(sort: kore.Sort, s: String, att: Attributes = Attributes()) extends kore.KToken

  case class KList(elements: List[K]) extends kore.KList {
    def items: java.util.List[K] = elements.asJava
  }

  case class KRewrite(left: kore.K, right: kore.K, att: Attributes = Attributes()) extends kore.KRewrite

  case class InjectedKLabel(klabel: kore.KLabel, att: Attributes) extends kore.InjectedKLabel

}
