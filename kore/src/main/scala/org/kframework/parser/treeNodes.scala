// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.parser

import org.kframework.attributes.Location
import org.kframework.definition.Production
import java.util._
import java.lang.Iterable
import collection.JavaConverters._
import org.apache.commons.lang3.StringEscapeUtils

trait Term {
  // TODO: add source
  val location: Optional[Location]
  def shallowCopy(l: Location): Term
}

trait ProductionReference extends Term {
  val production: Production
}

trait HasChildren {
  def items: Iterable[Term]
  def replaceChildren(newChildren: Collection[Term]): Term
}

case class Constant(value: String, production: Production, location: Optional[Location]) extends ProductionReference {
  def shallowCopy(location: Location) = Constant(value, production, Optional.of(location))
  override def toString = "#token(" + production.sort + ",\"" + StringEscapeUtils.escapeJava(value) + "\")"
}

case class TermCons(items: List[Term], production: Production, location: Optional[Location])
  extends ProductionReference with HasChildren {
  def shallowCopy(location: Location) = TermCons(items, production, Optional.of(location))

  def replaceChildren(newChildren: Collection[Term]) = {
    items.clear(); items.addAll(newChildren);
    this
  }
  override def toString() = production.klabel.getOrElse("NOKLABEL") + "(" + (items.asScala mkString ",") + ")"

  var cachedHashCode: Option[Int] = None

  def invalidateHashCode() {
    cachedHashCode = None
  }

  override def hashCode = cachedHashCode match {
    case None =>
      cachedHashCode  = Some(items.asScala.map(_.hashCode).fold(production.hashCode * 37)( 31 * _ + _))
      cachedHashCode.get
    case Some(hc) => hc
  }
}

case class Ambiguity(items: Set[Term], location: Optional[Location])
  extends Term with HasChildren {
  def shallowCopy(location: Location) = Ambiguity(items, Optional.of(location))
  def replaceChildren(newChildren: Collection[Term]) = {
    items.clear(); items.addAll(newChildren);
    this
  }
  override def toString() = "amb(" + (items.asScala mkString ",") + ")"
}

case class KList(items: List[Term], location: Optional[Location])
  extends Term with HasChildren {
  def add(t: Term) { items.add(t) }
  def shallowCopy(l: Location) = KList(items, location)
  def replaceChildren(newChildren: Collection[Term]) = {
    items.clear(); items.addAll(newChildren);
    this
  }
  override def toString() = "[" + (items.asScala mkString ",") + "]"
}

object TermCons {
  def apply(items: List[Term], production: Production): TermCons = TermCons(items, production, Optional.empty[Location])
}

object KList {
  def apply(items: List[Term]): KList = new KList(items, Optional.empty[Location]())
  @annotation.varargs def apply(ts: Term*): KList = KList(new ArrayList(ts.asJava))
  def apply(toCopy: KList): KList = KList(new ArrayList(toCopy.items)) // change when making the classes mutable
}

object Ambiguity {
  def apply(items: List[Term]): Ambiguity = new Ambiguity(new HashSet(items), Optional.empty())
  @annotation.varargs def apply(items: Term*): Ambiguity = Ambiguity(items.toList.asJava)
}
