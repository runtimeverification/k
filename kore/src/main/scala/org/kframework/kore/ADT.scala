package org.kframework.kore

import org.kframework.kore
import org.kframework.attributes._

object ADT {

  case class KLabel(name: String) extends kore.KLabel

  case class KApply(klabel: kore.KLabel, klist: kore.KList, att: Attributes = Attributes()) extends kore.KApply

  case class KSequence(left: kore.K, right: kore.K, att: Attributes = Attributes()) extends kore.KSequence

  case class KVariable(name: String, att: Attributes = Attributes()) extends kore.KVariable

  case class Sort(name: String) extends kore.Sort

  case class KToken(sort: kore.Sort, s: String, att: Attributes = Attributes()) extends kore.KToken

  case class KList(items: java.lang.Iterable[kore.K]) extends kore.KList

  case class KRewrite(left: kore.K, right: kore.K, att: Attributes = Attributes()) extends kore.KRewrite

}
