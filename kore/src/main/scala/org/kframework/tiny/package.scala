package org.kframework

package object tiny {
  type Sort = kore.Sort

  val True = And()(FreeTheory)
  val False = Or()(FreeTheory)
}
