// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework.parser

import java.util._
import org.kframework.attributes.HasLocation
import org.kframework.attributes.Location
import org.kframework.attributes.Source
import org.kframework.definition.Production
import org.kframework.kore.KORE.Sort
import org.kframework.utils.StringUtil
import org.pcollections.ConsPStack
import org.pcollections.PStack
import scala.jdk.CollectionConverters._

trait Term extends HasLocation {
  var location: Optional[Location] = Optional.empty()
  var source: Optional[Source]     = Optional.empty()
}

trait ProductionReference extends Term {
  val production: Production
}

trait HasChildren {
  def items: java.lang.Iterable[Term]

  def replaceChildren(newChildren: java.util.Collection[Term]): Term
}

case class Constant private (value: String, production: Production) extends ProductionReference {
  override def toString: String =
    "#token(" + production.sort + "," + StringUtil.enquoteKString(value) + ")"

  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(Constant.this)
}

// note that items is reversed because it is more efficient to generate it this way during parsing
case class TermCons private (items: PStack[Term], production: Production)
    extends ProductionReference
    with HasChildren {
  def get(i: Int): Term = items.get(items.size() - 1 - i)

  def `with`(i: Int, e: Term): TermCons =
    TermCons(items.`with`(items.size() - 1 - i, e), production, location, source)

  def replaceChildren(newChildren: java.util.Collection[Term]): TermCons =
    TermCons(ConsPStack.from(newChildren), production, location, source)

  override def toString: String = new TreeNodesToKORE(s => Sort(s)).apply(this).toString()

  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(TermCons.this)
}

case class Ambiguity(items: java.util.Set[Term]) extends Term with HasChildren {
  def replaceChildren(newChildren: java.util.Collection[Term]): Ambiguity =
    Ambiguity(new java.util.HashSet[Term](newChildren), location, source)

  override def toString: String = "amb(" + (items.asScala.mkString(",")) + ")"

  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(Ambiguity.this)
}

object Constant {
  def apply(
      value: String,
      production: Production,
      location: Optional[Location],
      source: Optional[Source]
  ): Constant = {
    val res = Constant(value, production)
    res.location = location
    res.source = source
    res
  }
}

object TermCons {
  def apply(
      items: PStack[Term],
      production: Production,
      location: Optional[Location],
      source: Optional[Source]
  ): TermCons = {
    val res = TermCons(items, production)
    res.location = location
    res.source = source
    res
  }

  def apply(
      items: PStack[Term],
      production: Production,
      location: Location,
      source: Source
  ): TermCons = TermCons(
    items,
    production,
    Optional.of(location),
    Optional.of(source)
  )
}

object Ambiguity {
  @annotation.varargs
  def apply(items: Term*): Ambiguity = Ambiguity(items.to(collection.mutable.Set).asJava)

  def apply(
      items: java.util.Set[Term],
      location: Optional[Location],
      source: Optional[Source]
  ): Ambiguity = {
    val res = Ambiguity(items)
    res.location = location
    res.source = source
    res
  }
}
