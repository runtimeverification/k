// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.builtin

import org.kframework.kore.KORE.Sort

object Sorts {
  val KString = Sort("KString")
  val KBoolean = Sort("KBoolean")
  val Int = Sort("Int")

  val K = Sort("K")
  val KVariable = Sort("KVariable")
  val KList = Sort("KList")
  val KToken = Sort("KToken")
}
