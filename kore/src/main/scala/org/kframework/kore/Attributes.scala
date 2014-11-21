package org.kframework.kore

case class Attributes(att: Set[K] = Set()) extends AttributesToString 

object Attributes {
  def apply(ks: K*) = new Attributes(ks.toSet)
}