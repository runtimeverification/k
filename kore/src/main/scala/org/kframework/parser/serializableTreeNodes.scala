// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework.parser

import org.kframework.attributes.{Location, Source}
import org.kframework.definition.Production

import java.util
import scala.collection.JavaConverters._

/**
 * Duplicate of Term, Constant, TermCons because they are not Serializable.
 * It was easier at this time to duplicate the classes and convert between them
 * than to change all the occurrences in the code.
 */

trait STerm {
  def location: Location
  def source: Source
  def production: Production
}

case class SConstant private(value: String, production: Production, location: Location, source: Source) extends STerm with Serializable {
}

case class STermCons private(items: java.util.List[STerm], production: Production, location: Location, source: Source) extends STerm with Serializable {
}

object STermViz {
  def from(f: java.util.function.UnaryOperator[STerm], name:String):STermViz = STermViz(f(_), name)

  def apply(f: STerm => STerm, name: String): STermViz = f match {
    case f: STermViz => f
    case _ => new STermViz(f, name)
  }
}

class STermViz(f: STerm => STerm, name: String) extends (STerm => STerm) {
  override def apply(input: STerm): STerm = {
    input match {
      case c: SConstant => f(c)
      case tc: STermCons =>
        f(tc)
        tc.items.forEach(apply)
        tc
    }
  }
}

object ToSerializable {
  def apply(t: Term): STerm =
    t match {
      case tc@TermCons(items, prod) => STermCons.apply(
        new util.ArrayList(items).asScala.reverse map apply asJava
        , prod, tc.location.get(), tc.source.get())
      case c@Constant(str, prod) => SConstant(str, prod, c.location.get(), c.source.get())
    }
}
