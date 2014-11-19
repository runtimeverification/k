// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

import collection.JavaConverters._
import KORE._

class KSet(private val backingSet: Set[K]) extends collection.AbstractSet[K] with KCollection {
  def contains(key: K): Boolean = backingSet.contains(key)
  def iterator: Iterator[K] = backingSet.iterator
  def +(elem: K): KSet = new KSet(backingSet + elem)
  def -(elem: K): KSet = new KSet(backingSet - elem)

  def matchAll(pattern: K, condition: K): Set[Map[KVariable, K]] = ???
}
