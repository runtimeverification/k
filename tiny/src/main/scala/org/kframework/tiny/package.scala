package org.kframework

import org.kframework.attributes.Att

package object tiny {
  type Sort = kore.Sort

  type Rule = K => Set[K]

  lazy val True = new And(Set(), Att())
  lazy val False = new Or(Set(), Att())

//  def ins[T](x: T) = { println(x); x }

  implicit class WithIns[T](x: T) {
    def ins = { println(x); x }
  }

}
