// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.builtin

import org.kframework.koreimplementation.UninterpretedSort
import org.kframework.koreimplementation.KLabel
import org.kframework.koreimplementation.UninterpretedSort

object Sorts {
  val KString = UninterpretedSort("KString")
  val KBoolean = UninterpretedSort("KBoolean")
  val Int = UninterpretedSort("Int")

  val K = UninterpretedSort("K")
  val KVariable = UninterpretedSort("KVariable")
  val KList = UninterpretedSort("KList")
  val KToken = UninterpretedSort("KToken")
}
