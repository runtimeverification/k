// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.parser

import org.kframework.attributes.{Source, Location}
import org.kframework.definition.Production
import java.util._
import java.lang.Iterable
import org.pcollections.{ConsPStack, PStack}
import collection.JavaConverters._
import org.apache.commons.lang3.StringEscapeUtils

import scala.collection.mutable;

trait Term {
  var location: Optional[Location] = Optional.empty()
  var source: Optional[Source] = Optional.empty()
}

trait ProductionReference extends Term {
  val production: Production
}

trait HasChildren {
  def items: Iterable[Term]
  def replaceChildren(newChildren: Collection[Term]): Term
}

case class Constant private(value: String, production: Production) extends ProductionReference {
  override def toString = "#token(" + production.sort + ",\"" + StringEscapeUtils.escapeJava(value) + "\")"
}

// note that items is reversed because it is more efficient to generate it this way during parsing
case class TermCons private(items: PStack[Term], production: Production)
  extends ProductionReference with HasChildren {
  def get(i: Int) = items.get(items.size() - 1 - i)
  def `with`(i: Int, e: Term) = TermCons(items.`with`(items.size() - 1 - i, e), production, location, source)

  def replaceChildren(newChildren: Collection[Term]) = TermCons(ConsPStack.from(newChildren), production, location, source)
  override def toString() = production.klabel.getOrElse("NOKLABEL") + "(" + (new ArrayList(items).asScala.reverse mkString ",") + ")"

  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(TermCons.this);
}

case class Ambiguity(items: Set[Term])
  extends Term with HasChildren {
  def replaceChildren(newChildren: Collection[Term]) = {
    items.clear(); items.addAll(newChildren);
    this
  }
  override def toString() = "amb(" + (items.asScala mkString ",") + ")"
}

case class KList(items: PStack[Term])
  extends Term with HasChildren {
  def add(t: Term) = KList(items.plus(t), location, source)
  def remove(n: Int) = {
    var newItems = items;
    for (_ <- 1 to n) {
      newItems = items.minus(0)
    }
    KList(newItems, location, source)
  }
  def replaceChildren(newChildren: Collection[Term]) = KList(ConsPStack.from(newChildren), location, source)
  override def toString() = "[" + (new ArrayList(items).asScala.reverse mkString ",") + "]"
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(KList.this);
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
  def apply(items: PStack[Term], production: Production, location: Optional[Location], source: Optional[Source]):TermCons = {
    val res = TermCons(items, production)
    res.location = location
    res.source = source
    res
  }

  def apply(items: PStack[Term], production: Production, location: Location, source: Source):TermCons = TermCons(items, production, Optional.of(location), Optional.of(source))
}

object KList {
  def apply(toCopy: KList): KList = KList(toCopy.items, toCopy.location, toCopy.source) // change when making the classes mutable
  def apply(items: PStack[Term], location: Optional[Location], source: Optional[Source]):KList = {
    val res = KList(items)
    res.location = location
    res.source = source
    res
  }
}

object Ambiguity {
  @annotation.varargs def apply(items: Term*): Ambiguity = Ambiguity(items.to[mutable.Set].asJava)
  def apply(items: Set[Term], location: Location, source: Source):Ambiguity = {
    val res = Ambiguity(items)
    res.location = Optional.of(location)
    res.source = Optional.of(source)
    res
  }
}
