// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import KORE._
import scala.Enumeration
import org.kframework.kore.outer.Associativity
import java.lang.invoke.MethodType
import java.lang.invoke.MethodHandles
import collection.JavaConverters._
import org.kframework.builtin.Sorts

object Meta extends (Any => K) {
  type HasProductIterator = { def productIterator: Iterator[Any] }

  def apply(o: Any): K = {
    o match {
      case o: List[_] => 'List(o map apply)
      case o: Set[_] => 'Set(o map apply toList)

      // Primitives
      case o: Int => KToken(Sorts.KInt, o.toString)
      case o: String => KToken(Sorts.KString, o.toString)
      case o: Boolean => KToken(Sort("Boolean"), o.toString)

      case o: Associativity.Value => KToken(Sort("Associativity"), o.toString)
      case o: java.io.File => KToken(Sort("File"), o.toString)

      // Already K
      case o: K => o

      case o: Sort => 'Sort(KToken(Sorts.KString, o.name))

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

object Concrete extends (K => Any) {
  import scala.reflect.runtime.{ universe => ru }
  val m = ru.runtimeMirror(getClass.getClassLoader)

  def apply(o: K) = {
    val res = o match {
      case KApply(KLabel("List"), ks, att) => ks.delegate map apply
      case KApply(KLabel("Seq"), ks, att) => ks.delegate map apply
      case KApply(KLabel("Set"), ks, att) => ks.delegate map apply toSet

      case KApply(KLabel(l), ks, att) =>
        val children = ks map { apply _ }

        val moduleS = try {
          m.staticModule("org.kframework.kore.outer." + l)
        } catch {
          case e: ScalaReflectionException => m.staticModule("org.kframework.kore." + l)
        }

        val moduleR = m.reflectModule(moduleS)
        val module = moduleR.instance

        val methodRef = module.getClass.getMethods()
          .filter { m => m.getName == "apply" && m.getParameterCount == children.size }
          .filter {
            m =>
              m.getParameterTypes.zip(children map { _.getClass }).exists {
                case (paramClass, argClass) => paramClass.isAssignableFrom(argClass)
              }
          } head

        //        println("invoking: " + methodRef +
        //          "\n on " + module +
        //          "\n with arguments: " + children +
        //          "\n of types: " + children.map(_.getClass))

        methodRef.invoke(module, children.toSeq.asInstanceOf[Seq[Object]]: _*)

      //      case KInt(x, _) => x
      //      case s: KSet => s.delegate map apply
      //      case s: KString => s.s
    }
    //    println(o + " concretized to " + res)
    res
  }
}
