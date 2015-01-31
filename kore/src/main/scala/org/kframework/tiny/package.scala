package org.kframework

package object tiny {
  type Sort = kore.Sort
  def Sort(s: String) = kore.ADT.Sort(s)

  val True = And()
  val False = Or()
}
