package org.kframework.tiny

import org.kframework.kore
import org.kframework.kore.KList
import org.kframework.definition
import org.kframework.attributes._

class Constructors(module: definition.Module) extends kore.Constructors {

  override def KLabel(name: String): KLabel = KLabel(name)
  override def KApply(klabel: kore.KLabel, klist: kore.KList, att: Attributes): kore.KApply = ???
  override def KSequence(left: kore.K, right: kore.K, att: Attributes): kore.KSequence = ???
  override def KVariable(name: String, att: Attributes): kore.KVariable = ???
  override def Sort(name: String): kore.Sort = ???
  override def KToken(sort: kore.Sort, s: String, att: Attributes): kore.KToken = ???
  override def KRewrite(left: kore.K, right: kore.K, att: Attributes): kore.KRewrite = ???
  override def KList(items: java.lang.Iterable[kore.K]): KList = ???
}
