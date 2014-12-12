// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.parser

import org.kframework.kore.outer.Production
import java.util._
import java.lang.Iterable
import collection.JavaConverters._

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
  def shallowCopy(newChildren: Collection[Term]): Term
}

case class Constant(s: String, production: Production, location: Optional[Location]) extends ProductionReference {
  def shallowCopy(l: Location) = Constant(s, production, location)
}

case class TermCons(items: List[Term], production: Production, location: Optional[Location])
  extends ProductionReference with HasChildren {
  def shallowCopy(l: Location) = TermCons(items, production, location)

  def shallowCopy(newChildren: Collection[Term]) = {
    items.clear(); items.addAll(newChildren);
    this
  }
}

case class Ambiguity(items: Set[Term], location: Optional[Location])
  extends Term with HasChildren {
  def shallowCopy(l: Location) = Ambiguity(items, location)
  def shallowCopy(newChildren: Collection[Term]) = {
    items.clear(); items.addAll(newChildren);
    this
  }
}

case class KList(items: List[Term], location: Optional[Location])
  extends Term with HasChildren {
  def add(t: Term) { items.add(t) }
  def shallowCopy(l: Location) = KList(items, location)
  def shallowCopy(newChildren: Collection[Term]) = {
    items.clear(); items.addAll(newChildren);
    this
  }
}

object TermCons {
  def apply(items: List[Term], production: Production): TermCons = TermCons(items, production, Optional.empty[Location])
}

object KList {
  def apply(items: List[Term]): KList = new KList(items, Optional.empty[Location]())
  @annotation.varargs def apply(ts: Term*): KList = KList(ts.asJava)
  def apply(toCopy: KList): KList = KList(new ArrayList(toCopy.items)) // change when making the classes mutable
}

object Ambiguity {
  def apply(items: List[Term]): Ambiguity = new Ambiguity(items.asScala.toSet.asJava, Optional.empty())
  def apply(items: Term*): Ambiguity = Ambiguity(items.toList.asJava)
}

case class Location(startLine: Int, startColumn: Int, endLine: Int, endColumn: Int)
