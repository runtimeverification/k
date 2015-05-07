// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.builtin

import org.kframework.kore.ADT
import org.kframework.kore.KORE.Sort

object Sorts {
  val KString = Sort("KString")
  val String = Sort("String")

  val KBool = Sort("KBool")
  val Bool = Sort("Bool")

  val Int = Sort("Int")
  val File = Sort("File")

  val K = Sort("K")
  val KBott = Sort("KBott")
  val KVariable = Sort("KVariable")
  val KItem = Sort("KItem")
  val KLabel = Sort("KLabel")
  val KList = Sort("KList")
  val KToken = Sort("KToken")

  val Id = ADT.Sort("Id")
  val KSeq = ADT.Sort("KSequence")
}
