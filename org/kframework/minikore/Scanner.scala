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
    } else { // end of file
      throw new java.io.EOFException()
    }
  }

  // abstract unreadable stream: next(), putback()
  var lookahead: Option[Char] = None
  //
  def nextWithSpaces(): Char = {
    lookahead match {
      case Some(c) =>
        lookahead = None
        c
      case None =>
        if (input.hasNext) {
          columnNum += 1
          input.next()
        } else { // end of line
          readLine()
          nextWithSpaces()
        }
    }
  }
  def next(): Char = {
    consumeWhiteSpaces()
    nextWithSpaces()
  }
  def putback(c: Char): Unit = {
    lookahead match {
      case Some(_) => ???
      case None =>
        lookahead = Some(c)
    }
  }

  def consumeWhiteSpaces(): Unit = {
    nextWithSpaces() match {
      case ' '  => consumeWhiteSpaces() // skip white spaces
      case '\t' => columnNum += 3; consumeWhiteSpaces() // skip white spaces
      case '\n' | '\r' => ??? // next() // stream.getLines implicitly drops newline characters
      case c => putback(c)
    }
  }

}
