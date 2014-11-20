package org.kframework.kore

final class Attributes(val klist: KList) extends KListBacked[Attributes] with AttributesToString {
  import KList.seqOfKtoKList
  // we will eventually decide on something much more specific for attributes
  def copy(klist: Iterable[K]) = new Attributes(KList(klist.toSeq: _*))
}

object Attributes extends CanBuildKListLike[Attributes] {
  def apply(klist: KList): Attributes = new Attributes(klist)
  def apply(list: K*): Attributes = new Attributes(list)
}

case class WithAttributes(k: K, att: Attributes) extends KItem