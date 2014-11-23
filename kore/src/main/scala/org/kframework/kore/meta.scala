// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import KORE._
import scala.Enumeration
import org.kframework.kore.outer.Associativity

object Meta extends App {
  type HasProductIterator = { def productIterator: Iterator[Any] }

  def apply(o: Any): K = {
    o match {
      case o: List[_] => KList(o map apply)
      case o: Set[_] => 'KSet(o.toList map apply)
      case o: Iterable[_] => 'KSet(o.toList map apply)
      case o if o.getClass().getMethods.exists(_.toString().contains("productIterator")) =>
        val elements = o.asInstanceOf[HasProductIterator].productIterator.toList
        KApply(KLabel(processName(o.getClass().getName)), elements map apply)
      case o: Int => KInt(o)
      case o: String => KToken(Sort("String"), o)
      case o: Boolean => KToken(Sort("Boolean"), o.toString)
      case o: Associativity.Value => KToken(Sort("Associativity"), o.toString)
      case o: java.io.File => KToken(Sort("File"), o.toString)
    }
  }

  def processName(arg: String) = {
    arg.replace("org.kframework.kore.outer.", "").replace("org.kframework.kore.", "")
  }
}