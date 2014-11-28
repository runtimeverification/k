// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import KORE._
import scala.Enumeration
import org.kframework.kore.outer.Associativity

object Meta extends (Any => K) {
  type HasProductIterator = { def productIterator: Iterator[Any] }

  def apply(o: Any): K = {
    o match {
      case o: List[_] => KList(o map apply)
      case o: Set[_] => new KSet(o map apply)
      case o: Iterable[_] => new KSet(o.toSet map apply)

      // Primitives
      case o: Int => KInt(o)
      case o: String => KToken(Sort("String"), o)
      case o: Boolean => KToken(Sort("Boolean"), o.toString)
      case o: Associativity.Value => KToken(Sort("Associativity"), o.toString)
      case o: java.io.File => KToken(Sort("File"), o.toString)

      // Already K
      case o: K => o

      // Fallback to reflection
      case o if o.getClass().getMethods.exists(_.toString().contains("productIterator")) =>
        val elements = o.asInstanceOf[HasProductIterator].productIterator.toList
        KApply(KLabel(processName(o.getClass().getName)), elements map apply)
    }
  }

  def processName(arg: String) = {
    arg.replace("org.kframework.kore.outer.", "").replace("org.kframework.kore.", "")
  }
}

case class Concrete(includes: Set[String]) extends (K => Any) {
  import scala.reflect.runtime.{ universe => ru }
  val m = ru.runtimeMirror(getClass.getClassLoader)

  def apply(o: K) = o match {
    case KApply(KLabel(l), ks, att) =>
      val children = ks map { apply _ }

      val moduleS = m.staticModule("org.kframework.kore." + l)
      val moduleR = m.reflectModule(moduleS)
      val module = moduleR.instance

      val paramTypes = children map { _.getClass() }

      val constructor = module.getClass.getMethod("apply", paramTypes: _*)

      println(module)
      println(constructor)

    case KInt(x, _) => x
  }
}
