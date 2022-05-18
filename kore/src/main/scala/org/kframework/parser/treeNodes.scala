// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework.parser

import org.kframework.attributes.{Source, Location, HasLocation}
import org.kframework.definition.Production
import org.kframework.kore.KORE.Sort
import java.util._
import java.lang.Iterable
import org.pcollections.{ConsPStack, PStack}
import collection.JavaConverters._
import org.kframework.utils.StringUtil

import scala.collection.mutable;

trait Term extends HasLocation {
  var location: Optional[Location] = Optional.empty()
  var source: Optional[Source] = Optional.empty()
}

trait ProductionReference extends Term {
  val production: Production
  var id: Optional[Integer] = Optional.empty()
  def setId(id: Optional[Integer]) {
    this.id = id
  }
}

trait HasChildren {
  def items: Iterable[Term]
  def replaceChildren(newChildren: Collection[Term]): Term
}

case class Constant private(value: String, production: Production) extends ProductionReference {
  override def toString = "#token(" + production.sort + "," + StringUtil.enquoteKString(value) + ")"
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(Constant.this);
}

// note that items is reversed because it is more efficient to generate it this way during parsing
case class TermCons private(items: PStack[Term], production: Production)
  extends ProductionReference with HasChildren {
  def get(i: Int) = items.get(items.size() - 1 - i)
  def `with`(i: Int, e: Term) = TermCons(items.`with`(items.size() - 1 - i, e), production, location, source, id)

  def replaceChildren(newChildren: Collection[Term]) = TermCons(ConsPStack.from(newChildren), production, location, source, id)
  override def toString() = new TreeNodesToKORE(s => Sort(s), false).apply(this).toString()

  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(TermCons.this);
}

case class Ambiguity(items: Set[Term])
  extends Term with HasChildren {
  def replaceChildren(newChildren: Collection[Term]) = Ambiguity(new HashSet[Term](newChildren), location, source)
  override def toString() = "amb(" + (items.asScala mkString ",") + ")"
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(Ambiguity.this);
}

object Constant {
  def apply(value: String, production: Production, location: Optional[Location], source: Optional[Source]):Constant = {
    val res = Constant(value, production)
    res.location = location
    res.source = source
    res
  }
}

object TermCons {
  def apply(items: PStack[Term], production: Production, location: Optional[Location], source: Optional[Source], id: Optional[Integer]):TermCons = {
    val res = TermCons(items, production)
    res.location = location
    res.source = source
    res.id = id
    res
  }

  def apply(items: PStack[Term], production: Production, location: Optional[Location], source: Optional[Source]):TermCons = {
    TermCons(items, production, location, source, Optional.empty())
  }

  def apply(items: PStack[Term], production: Production, location: Location, source: Source):TermCons = TermCons(items, production, Optional.of(location), Optional.of(source), Optional.empty())
}

object Ambiguity {
  @annotation.varargs def apply(items: Term*): Ambiguity = Ambiguity(items.to[mutable.Set].asJava)
  def apply(items: Set[Term], location: Optional[Location], source: Optional[Source]):Ambiguity = {
    val res = Ambiguity(items)
    res.location = location
    res.source = source
    res
  }
}
