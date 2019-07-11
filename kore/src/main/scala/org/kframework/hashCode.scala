package org.kframework

trait HasCachedHashCode {
  lazy val cachedHashCode = computeHashCode
  override def hashCode = cachedHashCode
  def computeHashCode: Int
}
