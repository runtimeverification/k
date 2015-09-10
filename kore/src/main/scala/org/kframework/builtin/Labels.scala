package org.kframework.builtin

import org.kframework.kore.{K, Constructors}

object Labels {
  val Hole = "HOLE"
  val KBag = "KBag"
  val And = "_andBool_"
  val Or = "_orBool_"
  val Cells = "#cells"
}

class Labels[KK <: K](cons: Constructors[KK]) {

  import cons._

  lazy val Hole = KLabel(Labels.Hole)
  lazy val KBag = KLabel(Labels.KBag)
  lazy val And = KLabel(Labels.And)
  lazy val Or = KLabel(Labels.Or)
}
