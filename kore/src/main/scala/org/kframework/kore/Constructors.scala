// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

import java.util.List
import scala.collection.Seq
import collection.JavaConverters._
import org.kframework.kore
import org.kframework.Collector
import org.kframework.CombinerFromBuilder

/**
 *
 * Helper constructors for KORE classes. The class is meant to be imported
 * statically.
 *
 * @see org.kframework.kore.InterfaceTest
 *
 */

object Constructors {
  def Attributes(ks: Set[K]) = kore.Attributes(ks)
  @annotation.varargs def Attributes(ks: K*) = kore.Attributes(ks: _*)

  def KString(s: String) = kore.KString(s);

  def Hole = kore.Hole

  def KBagLabel = kore.KBag

  @annotation.varargs def KBag(ks: K*) = kore.KBag(ks)

  def KBag(ks: KList) = kore.KBag(ks);

  def Sort(name: String) = kore.Sort(name);

  def KLabel(name: String) = kore.KLabel(name);

  @annotation.varargs def KList(ks: K*): KList = kore.KList(ks)

  def KList(ks: java.lang.Iterable[K]): KList = KList(ks.asScala.toSeq: _*)

  def KApply(klabel: KLabel, klist: KList, att: Attributes) = kore.KApply(klabel, klist, att)

  def KApply(klabel: KLabel, klist: KList) = kore.KApply(klabel, klist, Attributes())

  def KToken(sort: Sort, string: KString, att: Attributes) = kore.KToken(sort, string, att)
  def KToken(sort: Sort, string: KString) = kore.KToken(sort, string, Attributes())

  def KVariable(name: String, att: Attributes) = kore.KVariable(name, att)

  def KVariable(name: String) = {
    kore.KVariable(name, Attributes())
  }

  @annotation.varargs def KSequence(ks: K*) = kore.KSequence(ks)

  def KSequence(ks: java.util.List[K]) = kore.KSequence(KList(ks))

  def KRewrite(left: K, right: K) = kore.KRewrite(left, right, Attributes())

  def KRewrite(left: K, right: K, att: Attributes) = kore.KRewrite(left, right, att)
  
  def KInt(n: Int) = kore.KInt(n)
  
  def stream(c: KCollection) = org.kframework.Collections.stream(c);
  
  def toKList: Collector[K, KList] =
    Collector(() => new CombinerFromBuilder(kore.KList.newBuilder))
}
