// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

trait Sort extends SortToString {
  def name: String
}

object Sort {
  def apply(s: String) = UninterpretedSort(s)
  def unapply(s: Sort): Option[String] = Some(s.name)
}

case class UninterpretedSort(name: String) extends Sort
