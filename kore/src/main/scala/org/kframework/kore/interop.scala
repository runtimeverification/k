// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import collection.JavaConverters._

object Interface1 {
  import outer._
  import org.kframework.kore

  def immutable[T](s: java.util.Set[T]): Set[T] = s.asScala.toSet
  def immutable1[T](s: java.util.Set[T]): KList = null

  def KList(s: java.util.Set[K]): KList = kore.KList(s.asScala.toSeq: _*)
  def Definition(requires: Set[Require], modules: Set[Module]) =
    kore.outer.Definition(requires, modules)

  def Require(file: java.io.File) = kore.outer.Require(file)
  def Module(name: String, sentences: Set[Sentence], att: Attributes) =
    kore.outer.Module(name, sentences, att)
}