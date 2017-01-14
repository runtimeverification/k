package org.kframework.minikore

class Scanner {
  // should be used after `init()`

  private var stream: io.Source = _
  private var lines: Iterator[String] = _
  var input: Iterator[Char] = _
  var line: String = _
  var lineNum: Int = _
  var columnNum: Int = _

  def init(file: java.io.File): Unit = {
    init(io.Source.fromFile(file))
  }
  def init(src: io.Source): Unit = {
    stream = src
    lines = stream.getLines()
    line = ""
    lineNum = 0
    columnNum = 0
    readLine()
  }

  def close(): Unit = {
    stream.close()
  }

  def readLine(): Unit = {
    if (lines.hasNext) {
      line = lines.next()
      input = line.iterator
      lineNum += 1
      columnNum = 0
    } else { // end of file
      throw new java.io.EOFException()
    }
  }

  // abstract stream: next(), putback()
  var lookahead: Option[Char] = None
  var yieldEOL: Boolean = false
  //
  def next(): Char = {
    columnNum += 1
    lookahead match {
      case Some(c) =>
        lookahead = None
        c
      case None =>
        if (input.hasNext) {
          input.next()
        } else if (!yieldEOL) { // end of line
          yieldEOL = true
          '\n'
        } else {
          yieldEOL = false
          readLine()
          next()
        }
    }
  }
  def putback(c: Char): Unit = {
    columnNum -= 1
    lookahead match {
      case Some(_) => ???
      case None =>
        lookahead = Some(c)
    }
  }

  def skipWhitespaces(): Unit = {
    next() match {
      case ' '  => skipWhitespaces()
      case '\t' => columnNum += 3; skipWhitespaces()
      case '\n' | '\r' => skipWhitespaces()
      case c => putback(c)
    }
  }

  def nextWithSkippingWhitespaces(): Char = {
    skipWhitespaces()
    next()
  }

  def isEOF(): Boolean = {
    try {
      putback(nextWithSkippingWhitespaces())
      false
    } catch {
      case _: java.io.EOFException => true
      case _: Throwable => ???
    }
  }

}
