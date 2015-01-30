package org.kframework.kore

import java.lang.Iterable
import org.kframework.attributes._

object ADTConstructors extends Constructors {
  override def KLabel(name: String): KLabel = ADT.KLabel(name)

  override def KApply(klabel: KLabel, klist: KList, att: Attributes): KApply = ADT.KApply(klabel, klist, att)

  override def KSequence(left: K, right: K, att: Attributes): KSequence = ADT.KSequence(left, right, att)

  override def KVariable(name: String, att: Attributes): KVariable = ADT.KVariable(name, att)

  override def Sort(name: String): Sort = ADT.Sort(name)

  override def KToken(sort: Sort, s: String, att: Attributes): KToken = ADT.KToken(sort, s, att)

  override def KRewrite(left: K, right: K, att: Attributes): KRewrite = ADT.KRewrite(left, right, att)

  override def KList(items: Iterable[K]): KList = ADT.KList(items)

  import collection.JavaConverters._

  def KList(ks: K*): KList = ADT.KList(ks.asJava)
}

