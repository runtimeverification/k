// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.tiny

import org.kframework._
import koreimplementation._
import KORE._
import scala.Enumeration
import org.kframework.definition.Associativity
import java.lang.invoke.MethodType
import java.lang.invoke.MethodHandles
import collection.JavaConverters._
import org.kframework.builtin.Sorts

object Up extends (Any => K) {

  def apply(o: Any): K = {
    o match {
      case o: List[_] => 'List(o map apply)
      case o: Set[_] => 'Set(o map apply toList)

      // Primitives
      case o: Int => KToken(Sorts.Int, o.toString)
      case o: String => KToken(Sorts.KString, o.toString)
      case o: Boolean => KToken(Sort("Boolean"), o.toString)

      case o: Associativity.Value => KToken(Sort("Associativity"), o.toString)
      case o: java.io.File => KToken(Sort("File"), o.toString)

      // Already K
      case o: K => o

      case o: Sort => 'Sort(KToken(Sorts.KString, o.name))

      // Fallback to reflection
      case o: Product =>
        val elements = o.productIterator.toList
        val klist = elements map apply
        KApply(KLabel(processName(o.getClass().getName)), klist,
          Attributes() + (Attributes.classFromUp.toString(), o.getClass().getName()))
    }
  }

  def processName(arg: String) = {
    arg.replace("org.kframework.definition.", "").replace("org.kframework.koreimplementation.", "")
  }
}
