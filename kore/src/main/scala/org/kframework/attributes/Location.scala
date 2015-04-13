package org.kframework.attributes

case class Location(startLine: Int, startColumn: Int, endLine: Int, endColumn: Int) extends Comparable[Location] {
  import scala.math.Ordered.orderingToOrdered
  def compareTo(that: Location): Int = (startLine, startColumn, endLine, endColumn) compare (that.startLine, that.startColumn, that.endColumn, that.endColumn)
}

case class Source(source: String)