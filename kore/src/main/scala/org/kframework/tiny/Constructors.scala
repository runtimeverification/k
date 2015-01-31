package org.kframework.tiny

import org.kframework.attributes._
import org.kframework.kore.InjectedKLabel
import org.kframework.{kore, definition}

class Constructors(module: definition.Module) extends kore.Constructors {

  override def KLabel(name: String): KLabel = KLabel(name)
  override def KApply(klabel: kore.KLabel, klist: kore.KList, att: Attributes): kore.KApply = ???
  override def KSequence[KK <: kore.K](items: java.util.List[KK], att: Attributes): kore.KSequence = ???
  override def KVariable(name: String, att: Attributes): kore.KVariable = ???
  override def Sort(name: String): kore.Sort = ???
  override def KToken(sort: kore.Sort, s: String, att: Attributes): kore.KToken = ???
  override def KRewrite(left: kore.K, right: kore.K, att: Attributes): kore.KRewrite = ???
  override def KList[KK <: kore.K](items: java.util.List[KK]): kore.KList = ???
  override def InjectedKLabel(klabel: kore.KLabel, att: Attributes): InjectedKLabel = ???
}
