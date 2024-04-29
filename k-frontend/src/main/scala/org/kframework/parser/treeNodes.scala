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
import scala.collection.immutable
import scala.jdk.CollectionConverters._

sealed trait Term extends HasLocation {
  var location: Optional[Location] = Optional.empty()
  var source: Optional[Source]     = Optional.empty()
}

object Term {

  /**
   * Define an ordering on Terms as follows:
   *   - Any ProductionReference is < any Ambiguity
   *   - ProductionReferences are
   *     - First compared by their production
   *     - If their productions are equal, they are compared:
   *       - First by their number of children
   *       - Then lexicographically over their children
   *   - Ambiguities are compared
   *     - First by their number of children
   *     - Then lexicographically over the sorted order of their children
   */
  implicit val ord: Ordering[Term] = (a: Term, b: Term) =>
    (a, b) match {
      case (c: ProductionReference, d: Ambiguity) => -1
      case (c: Ambiguity, d: ProductionReference) => 1
      case (c: Ambiguity, d: Ambiguity)           => Ordering[Ambiguity].compare(c, d)
      case (c: ProductionReference, d: ProductionReference) =>
        Ordering[ProductionReference].compare(c, d)
    }

}

sealed trait ProductionReference extends Term {
  val production: Production
}

object ProductionReference {
  implicit val ord: Ordering[ProductionReference] =
    (a: ProductionReference, b: ProductionReference) =>
      (a, b) match {
        case (c: Constant, d: TermCons) => -1
        case (c: TermCons, d: Constant) => 1
        case (c: Constant, d: Constant) => Ordering[Constant].compare(c, d)
        case (c: TermCons, d: TermCons) => Ordering[TermCons].compare(c, d)
      }
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

  implicit val ord: Ordering[Constant] = (a: Constant, b: Constant) =>
    Ordering[Production].compare(a.production, b.production)
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

  implicit val ord: Ordering[TermCons] = (a: TermCons, b: TermCons) => {
    val prodComp = Ordering[Production].compare(a.production, b.production)
    if (prodComp != 0) {
      prodComp
    } else {
      Ordering.Implicits
        .seqOrdering[immutable.Seq, Term]
        .compare(
          org.kframework.Collections.immutable(a.items).reverse,
          org.kframework.Collections.immutable(b.items).reverse
        )
    }
  }
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

  implicit val ord: Ordering[Ambiguity] = (a: Ambiguity, b: Ambiguity) =>
    Ordering.Implicits
      .seqOrdering[immutable.Seq, Term]
      .compare(
        org.kframework.Collections.immutable(a.items).toSeq.sorted(Term.ord),
        org.kframework.Collections.immutable(b.items).toSeq.sorted(Term.ord)
      )
}
