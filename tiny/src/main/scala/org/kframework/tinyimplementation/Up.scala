// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.tinyimplementation

import org.kframework.attributes._
import org.kframework.builtin.Sorts
import org.kframework.definition.Associativity
import org.kframework.kore.{ADTConstructors => cons, _}

import scala.collection.JavaConverters._

object Up extends (Any => K) {

  implicit def symbolWithKApply(s: Symbol) = new {
    def apply(ks: K*): KApply = apply(ks.toList, Att())
    def apply(l: List[K], att: Att = Att()): KApply = {
      cons.KApply(cons.KLabel(s.name), cons.KList(l.asJava), att)
    }
  }

  def apply(o: Any): K = {
    o match {
      case o: List[_] => 'List(o map apply)
      case o: Set[_] => 'Set(o map apply toList)

      // Primitives
      case o: Int => cons.KToken(Sorts.Int, o.toString, Att())
      case o: String => cons.KToken(Sorts.KString, o.toString, Att())
      case o: Boolean => cons.KToken(cons.Sort("Boolean"), o.toString, Att())

      case o: Associativity.Value => cons.KToken(cons.Sort("Associativity"), o.toString, Att())
      case o: java.io.File => cons.KToken(cons.Sort("File"), o.toString, Att())

      // Already K
      case o: K => o

      case o: Sort => 'Sort(cons.KToken(Sorts.KString, o.name, Att()))

      // Fallback to reflection
      case o: Product =>
        val elements = o.productIterator.toList
        val klist = cons.KList(elements map apply asJava)
        cons.KApply(cons.KLabel(processName(o.getClass().getName)), klist,
          Att() +(ClassFromUp.toString(), o.getClass().getName()))
    }
  }

  def processName(arg: String) = {
    arg.replace("org.kframework.definition.", "").replace("org.kframework.koreimplementation.", "")
  }
}
