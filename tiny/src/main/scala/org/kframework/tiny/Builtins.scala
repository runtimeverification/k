package org.kframework.tiny

import org.kframework.kore.ADT

object Builtins {
  val Int = ADT.Sort("Int")
  val String = ADT.Sort("String")
  val Id = ADT.Sort("ID")
  val KSeq = ADT.Sort("~>")
}
