// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.koreimplementation

;

import java.util.List
import scala.collection.Seq
import collection.JavaConverters._
import org.kframework._
import org.kframework.Collector
import org.kframework.CombinerFromBuilder
import org.kframework.tinyimplementation.builtin
import org.kframework.attributes

/**
 *
 * Helper constructors for KORE classes. The class is meant to be imported
 * statically.
 *
 * @see org.kframework.koreimplementation.InterfaceTest
 *
 */

object Constructors {
  def Attributes(ks: Set[K]) = attributes.Attributes(ks)
  @annotation.varargs def Attributes(ks: K*) = attributes.Attributes(ks: _*)

  //  @annotation.varargs def KBag(ks: K*) = koreimplementation.KBag(ks)

  def Location(startLine: Int, startColumn: Int, endLine: Int, endColumn: Int) = Location(startLine, startColumn, endLine, endColumn)

  //  def KBag(ks: KList) = koreimplementation.KBag(ks);

  def Sort(name: String) = koreimplementation.Sort(name);

  def KLabel(name: String) = koreimplementation.KLabel(name);

  @annotation.varargs def KList(ks: K*): KList = koreimplementation.KList(ks)

  def KList(ks: java.lang.Iterable[K]): KList = KList(ks.asScala.toSeq: _*)

  def KApply(klabel: KLabel, klist: KList, att: attributes.Attributes) = koreimplementation.KApply(klabel, klist, att)

  def KApply(klabel: KLabel, klist: KList) = koreimplementation.KApply(klabel, klist, Attributes())

  def KToken(sort: Sort, string: String, att: attributes.Attributes) = koreimplementation.KToken(sort, string, att)
  def KToken(sort: Sort, string: String) = koreimplementation.KToken(sort, string, Attributes())

  def KVariable(name: String, att: attributes.Attributes) = koreimplementation.KVariable(name, att)

  def KVariable(name: String) = {
    koreimplementation.KVariable(name, Attributes())
  }

  def InjectedKLabel(l: KLabel) = koreimplementation.InjectedKLabel(l)
  def InjectedKList(l: KList) = koreimplementation.InjectedKList(l)

  @annotation.varargs def KSequence(ks: K*) = koreimplementation.KSequence(ks: _*)

  def KSequence(ks: java.util.List[K]) = koreimplementation.KSequence(ks.asScala.toList)

  def KRewrite(left: K, right: K) = koreimplementation.KRewrite(left, right, Attributes())

  def KRewrite(left: K, right: K, att: attributes.Attributes) = koreimplementation.KRewrite(left, right, att)

  //  def KInt(n: Int) = koreimplementation.KInt(n)

  def stream(c: KCollection) = org.kframework.Collections.stream(c);

  def toKList: Collector[K, KList] =
    Collector(() => new CombinerFromBuilder(koreimplementation.KList.newBuilder()))

  def toKSequence: Collector[K, KSequence] =
    Collector(() => new CombinerFromBuilder(koreimplementation.KSequence.newBuilder()))
}
