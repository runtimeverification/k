// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.koreimplementation

import org.kframework.kore._

object Sort {
  def apply(s: String) = UninterpretedSort(s)

  def unapply(s: Sort): Option[String] = Some(s.name)
}

case class UninterpretedSort(name: String) extends Sort {
  def apply(s: String) = KUninterpretedToken(this, s)
  override def toString = name
}
