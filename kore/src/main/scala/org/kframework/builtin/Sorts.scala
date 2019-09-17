// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework.builtin

import org.kframework.kore.ADT
import org.kframework.kore.KORE.Sort

object Sorts {
  val Layout = Sort("#Layout")

  val RuleTag = Sort("#RuleTag")

  val KString = Sort("KString")
  val KBool = Sort("KBool")

  val Bool = Sort("Bool")
  val Int = Sort("Int")
  val MInt = Sort("MInt")
  val String = Sort("String")
  val Float = Sort("Float")
  val StringBuffer = Sort("StringBuffer")
  val Bytes = Sort("Bytes")

  val List = Sort("List")
  val Set = Sort("Set")
  val Map = Sort("Map")

  val K = Sort("K")
  val KBott = Sort("KBott")
  val KVariable = Sort("#KVariable")
  val KItem = Sort("KItem")
  val KLabel = Sort("KLabel")
  val KResult = Sort("KResult")
  val KList = Sort("KList")
  val KConfigVar = Sort("KConfigVar")

  val Bag = Sort("Bag")
  val Cell = Sort("Cell")
  val CellName = Sort("#CellName");

  val GeneratedTopCell = Sort("GeneratedTopCell")
  val GeneratedCounterCell = Sort("GeneratedCounterCell")

  val Id = Sort("Id")

  val Z3Query  = Sort("Z3Query")
  val Z3Result = Sort("Z3Result")
}
