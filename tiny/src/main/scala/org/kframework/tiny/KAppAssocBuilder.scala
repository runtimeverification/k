// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.tiny

import scala.collection.mutable.Builder

class KAppAssocBuilder(val builder: Builder[K, List[K]], label: Label) extends Builder[K, List[K]] {
  def +=(k: K): this.type = {
    k match {
      case KApp(`label`, list, att) => list foreach builder.+=
      case k => builder += k
    }
    this
  }

  def clear(): Unit = builder.clear()

  def result(): List[K] = builder.result();
}
