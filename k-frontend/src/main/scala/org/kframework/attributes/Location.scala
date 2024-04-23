// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.attributes

case class Location(startLine: Int, startColumn: Int, endLine: Int, endColumn: Int)
    extends Comparable[Location]
    with AttValue {
  import scala.math.Ordered.orderingToOrdered
  def compareTo(that: Location): Int = (startLine, startColumn, endLine, endColumn).compare(
    that.startLine,
    that.startColumn,
    that.endLine,
    that.endColumn
  )
}

case class Source(source: String) extends Comparable[Source] with AttValue {
  def compareTo(that: Source): Int = this.source.compareTo(that.source)
}
