package org.kframework.kore.parser

import org.apache.commons.lang3.StringEscapeUtils
import org.kframework.kore._
import org.kframework.kore

/** Parsing error exception. */
case class ParseError(msg: String) extends Exception(msg) // ParseError.msg eq Exception.detailMessage, i.e., msg() == getMessage()

/** A parser for [[kore.Pattern]].
  *
  * @constructor Creates a new parser.
  */
class TextToKore(b: Builders) {
  private val scanner = new Scanner()

  /** Parses the file and returns [[kore.Definition]]. */
  @throws(classOf[ParseError])
  def parse(file: java.io.File): Definition = {
    parse(io.Source.fromFile(file))
  }

  /** Parses from the stream and returns [[kore.Definition]]. */
  @throws(classOf[ParseError])
  def parse(src: io.Source): Definition = {
    try {
      scanner.init(src)
      parseDefinition()
    } catch {
      case _: java.io.EOFException => throw ParseError("ERROR: Unexpected end of file while parsing")
      case exc: ParseError => throw exc
      case exc: Throwable => throw ParseError("ERROR: Unexpected error while parsing: " + exc.getMessage) // shouldn't be reachable
    } finally {
      scanner.close()
    }
  }

  // Definition = Attributes Modules
  private def parseDefinition(): Definition = {
    val att = parseAttributes()
    val modules = parseModules(Seq())
    b.Definition(att, modules)
  }

  // Attributes = [ List{Pattern, ',', ']'} ]
  private def parseAttributes(): Attributes = {
    consumeWithLeadingWhitespaces("[")
    val att = parseList(() => parsePattern(), ',', ']')
    consumeWithLeadingWhitespaces("]")
    b.Attributes(att)
  }

  // Modules = <EOF> // <empty>
  //         | Module Modules
  private def parseModules(modules: Seq[Module]): Seq[Module] = {
    if (scanner.isEOF()) modules
    else {
      val mod = parseModule()
      parseModules(modules :+ mod)
    }
  }

  // Module = module ModuleName Sentences endmodule Attributes
  private def parseModule(): Module = {
    consumeWithLeadingWhitespaces("module")
    val nameStr = parseModuleName()
    val sentences = parseSentences(Seq())
    consumeWithLeadingWhitespaces("endmodule")
    val att = parseAttributes()
    b.Module(b.ModuleName(nameStr), sentences, att)
  }

  // Sentences = <lookahead>(e) // <empty>
  //           | Sentence Sentences
  // Sentence = sort { SortVariableList } Sort Attributes
  //          | symbol Symbol ( SortList ) : Sort Attributes
  //          | alias Alias ( SortList ) : Sort Attributes
  //          | axiom { SortVariableList } Axiom
  private def parseSentences(sens: Seq[Sentence]): Seq[Sentence] = {
    val c1 = scanner.nextWithSkippingWhitespaces()
    if (c1 == 'e') { // endmodule
      scanner.putback('e')
      sens
    }
    else {
      val c2 = scanner.nextWithSkippingWhitespaces()
      (c1, c2) match {
        case ('i', 'm') => // import
          consume("port")
          val nameStr = parseModuleName()
          val att = parseAttributes()
          val sen = b.Import(b.ModuleName(nameStr), att)
          parseSentences(sens :+ sen)
        case ('s', 'o') => // sort senaration
          consume("rt")
          consumeWithLeadingWhitespaces("{")
          val params = parseList(() => parseSortVariable(), ',', '}')
          consumeWithLeadingWhitespaces("}")
          val sort = parseSort()
          val att = parseAttributes()
          val sen = b.SortDeclaration(params, sort, att)
          parseSentences(sens :+ sen)
        case ('s', 'y') => // symbol senaration
          consume("mbol")
          val symbol = parseSymbol()
          consumeWithLeadingWhitespaces("(")
          val argSorts = parseList(() => parseSort(), ',', ')')
          consumeWithLeadingWhitespaces(")")
          consumeWithLeadingWhitespaces(":")
          val returnSort = parseSort()
          val att = parseAttributes()
          val sen = b.SymbolDeclaration(symbol, argSorts, returnSort, att)
          parseSentences(sens :+ sen)
        case ('a', 'l') => // alias senaration
          consume("ias")
          val alias = parseAlias()
          consumeWithLeadingWhitespaces("(")
          val argSorts = parseList(() => parseSort(), ',', ')')
          consumeWithLeadingWhitespaces(")")
          consumeWithLeadingWhitespaces(":")
          val returnSort = parseSort()
          val att = parseAttributes()
          val sen = b.AliasDeclaration(alias, argSorts, returnSort, att)
          parseSentences(sens :+ sen)
        case ('a', 'x') => // axiom senaration
          consume("iom")
          consumeWithLeadingWhitespaces("{")
          val params = parseList(() => parseSortVariable(), ',', '}')
          consumeWithLeadingWhitespaces("}")
          val pattern = parsePattern()
          val att = parseAttributes()
          val sen = b.AxiomDeclaration(params, pattern, att)
          parseSentences(sens :+ sen)
        case (e1, e2) =>
          throw error("sort, symbol, alias, axiom", e1)
      }
    }
  }


  // Import = ModuleName Attributes
  private def parseImport(): Sentence = {
    val name = parseModuleName()
    val att = parseAttributes()
    b.Import(b.ModuleName(name), att)
  }

  // Pattern = Variable
  //         | SymbolOrAlias ( List{Pattern, ',', ')'} )
  //         | \top { Sort } ( )
  //         | \bottom { Sort } ( )
  //         | \and  { Sort } ( Pattern , Pattern )
  //         | \or  { Sort } ( Pattern , Pattern )
  //         | \not  { Sort } ( Pattern )
  //         | \implies  { Sort } ( Pattern , Pattern )
  //         | \iff  { Sort } ( Pattern , Pattern )
  //         | \exists  { Sort } ( Variable , Pattern )
  //         | \forall  { Sort } ( Variable , Pattern )
  //         | \next { Sort } ( Pattern )
  //         | \rewrites { Sort , Sort } ( Pattern , Pattern )
  //         | \equal  { Sort , Sort } ( Pattern , Pattern )
  //         | \mem { Sort , Sort } ( Variable , Pattern )
  //         | \subset { Sort , Sort } ( Pattern , Pattern )
  //         | \domainvalue ( StringLiteral , StringLiteral )  // this syntax is temporary.
  //         | StringLiteral
  private def parsePattern(): Pattern = {
    scanner.nextWithSkippingWhitespaces() match {
      case '"' => // string literals
        scanner.putback('"')
        val str = parseString()
        b.StringLiteral(str)
      case '\\' => // logic connectives
        val c1 = scanner.next()
        val c2 = scanner.next()
        (c1, c2) match {
          case ('t', 'o') => // top
            consume("p")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            consumeWithLeadingWhitespaces(")")
            b.Top(s)
          case ('b', 'o') => // bottom
            consume("ttom")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            consumeWithLeadingWhitespaces(")")
            b.Bottom(s)
          case ('a', 'n') => // and
            consume("d")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern()
            consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.And(s, p1, p2)
          case ('o', 'r') => // or
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern()
            consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Or(s, p1, p2)
          case ('n', 'o') => // not
            consume("t")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Not(s, p)
          case ('i', 'm') => // implies
            consume("plies")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern()
            consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Implies(s, p1, p2)
          case ('i', 'f') => // iff
            consume("f")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern()
            consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Iff(s, p1, p2)
          case ('e', 'x') => // exists
            consume("ists")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val v = parseVariable()
            consumeWithLeadingWhitespaces(",")
            val p = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Exists(s, v, p)
          case ('f', 'o') => // forall
            consume("rall")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val v = parseVariable()
            consumeWithLeadingWhitespaces(",")
            val p = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Forall(s, v, p)
          case ('n', 'e') => // next
            consume("xt")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Next(s, p)
          case ('r', 'e') => // rewrites
            consume("writes")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces(",")
            val rs = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern()
            consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Rewrites(s, rs, p1, p2)
          case ('e', 'q') => // equals
            consume("uals")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces(",")
            val rs = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern()
            consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Equals(s, rs, p1, p2)
          case ('m', 'e') => // mem
            consume("m")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces(",")
            val rs = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val x = parseVariable()
            consumeWithLeadingWhitespaces(",")
            val p = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Mem(s, rs, x, p)
          case ('s', 'u') => // subset
            consume("bset")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces(",")
            val rs = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern()
            consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Subset(s, rs, p1, p2)
          case ('d', 'o') => // domainvalue
            consume("mainvalue")
            consumeWithLeadingWhitespaces("(")
            val sortStr = parseString()
            consumeWithLeadingWhitespaces(",")
            val valueStr = parseString()
            consumeWithLeadingWhitespaces(")")
            b.DomainValue(sortStr, valueStr)
          case (err1, err2) =>
            val known = Seq(
              "\\top", "\\bottom", "\\and", "\\or", "\\implies",
              "\\iff", "\\exists", "\\forall",
              "\\next", "\\rewrites", "\\equals", "\\mem", "\\subset")
            throw error(known.mkString(","), "'\\" + err1 + err2 + "'")
        }
      case c => // variable or application
        scanner.putback(c)
        val id = parseId()
        scanner.nextWithSkippingWhitespaces() match {
          case ':' => // variable
            // TODO(Daejun): check if symbol is Name
            val sort = parseSort()
            b.Variable(id, sort)
          case '{' => // application: symbol or alias
            val params = parseList(() => parseSort(), ',', '}')
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val args = parseList(() => parsePattern(), ',', ')')
            consumeWithLeadingWhitespaces(")")
            b.Application(b.SymbolOrAlias(id, params), args)
          case err =>
            throw error("':' or '('", err)
        }
    }
  }

  // Variable = Name : Sort
  private def parseVariable(): Variable = {
    val name = parseId()
    consumeWithLeadingWhitespaces(":")
    val sort = parseSort()
    b.Variable(name, sort)
  }

  //////////////////////////////////////////////////////////

  // String = " <char> "
  private def parseString(): String = {
    def loop(s: StringBuilder): String = {
      scanner.next() match {
        case '"' =>
          s.toString()
        case '\\' =>
          val c = scanner.next()
          val s1 = StringEscapeUtils.unescapeJava("\\" + c)
          s ++= s1;
          loop(s)
        case c =>
          s += c; loop(s)
      }
    }

    scanner.nextWithSkippingWhitespaces() match {
      case '"' => loop(new StringBuilder())
      case err => throw error('"', err) // shouldn't be reachable
    }
  }

  // ModuleName = [A-Z][A-Z0-9-]*
  private def parseModuleName(): String = {
    def loop(s: StringBuilder): String = {
      scanner.next() match {
        case c if ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || c == '-' =>
          s += c; loop(s)
        case c => scanner.putback(c)
          s.toString()
      }
    }

    scanner.nextWithSkippingWhitespaces() match {
      case c if isModuleNameStart(c) => loop(new StringBuilder(c.toString))
      case err => throw error("<ModuleName>", err)
    }
  }

  private def isModuleNameStart(c: Char): Boolean = {
    'A' <= c && c <= 'Z'
  }

  // Sort = SortVariable | Name { List{Sort, ",", ")"} }
  private def parseSort(): Sort = {
    val name = parseId()
    scanner.next() match {
      case '{' =>
        val params = parseList(() => parseSort(), ',', '}')
        consumeWithLeadingWhitespaces("}")
        b.CompoundSort(name, params)
      case c =>
        scanner.putback(c)
        b.SortVariable(name)
    }
  }

  private def parseSortVariable(): SortVariable = {
    val name = parseId()
    b.SortVariable(name)
  }

  private def parseSymbol(): Symbol = {
    val ctr = parseId()
    consumeWithLeadingWhitespaces("{")
    val params = parseList(() => parseSort(), ',', '}')
    consumeWithLeadingWhitespaces("}")
    b.Symbol(ctr, params)
  }

  private def parseAlias(): Alias = {
    val ctr = parseId()
    consumeWithLeadingWhitespaces("{")
    val params = parseList(() => parseSort(), ',', '}')
    consumeWithLeadingWhitespaces("}")
    b.Alias(ctr, params)
  }

  private def parseId(): String = {
    def loop(s: StringBuilder): String = {
      scanner.next() match {
        case c if isSymbolChar(c) =>
          s += c; loop(s)
        case c => scanner.putback(c)
          s.toString()
      }
    }

    scanner.nextWithSkippingWhitespaces() match {
      // case '`' => scanner.putback('`')
      //   parseEscapedSymbol()
      case c if isSymbolChar(c) =>
        loop(new StringBuilder(c.toString))
      case err => throw error("<Symbol>", err)
    }
  }

  private def isSymbolChar(c: Char): Boolean = TextToKore.isSymbolChar(c) // TODO(Daejun): more efficient way?

  // EscapedSymbol = ` [^`] `
  // private def parseEscapedSymbol(): String = {
  //   def loop(s: StringBuilder): String = {
  //     scanner.next() match {
  //       case '`' =>
  //         s.toString()
  //       case c =>
  //         s += c; loop(s)
  //     }
  //   }

  //   scanner.nextWithSkippingWhitespaces() match {
  //     case '`' =>
  //       loop(new StringBuilder())
  //     case err => throw error('`', err) // shouldn't be reachable
  //   }
  // }

  // List{Elem, <sep>, <endsWith>}
  //
  // List = <endsWith> // <empty>
  //      | Elem List2
  // List2 = <endsWith> // <empty>
  //       | <sep> Elem List2
  private def parseList[T](parseElem: () => T, sep: Char, endsWith: Char): Seq[T] = {
    assert(sep != endsWith)

    def parseList2(lst: Seq[T]): Seq[T] = {
      scanner.nextWithSkippingWhitespaces() match {
        case c if c == endsWith => scanner.putback(c)
          lst
        case c if c == sep =>
          val elem = parseElem()
          parseList2(lst :+ elem)
        case err => throw error("'" + endsWith + "' or '" + sep + "'", err)
      }
    }

    scanner.nextWithSkippingWhitespaces() match {
      case c if c == endsWith => scanner.putback(c)
        Seq()
      case c => scanner.putback(c)
        val elem = parseElem()
        parseList2(Seq(elem))
    }
  }

  private def consumeWithLeadingWhitespaces(str: String): Unit = {
    scanner.skipWhitespaces()
    consume(str)
  }

  private def consume(str: String): Unit = {
    for (c <- str) {
      val n = scanner.next()
      if (n == c) ()
      else throw error(c, n)
    }
  }

  //////////////////////////////////////////////////////////

  private def error(expected: String, actual: String): ParseError = {
    ParseError(
      "ERROR: " + "Line " + scanner.lineNum + ": Column " + scanner.columnNum + ": " +
        "Expected " + expected + ", but " + actual // StringEscapeUtils.escapeJava(actual)
        + System.lineSeparator() + scanner.line + System.lineSeparator() +
        List.fill(scanner.columnNum - 1)(' ').mkString + "^"
    )
  }

  private def error(expected: String, actual: Char): ParseError = {
    error(expected, "'" + actual + "'")
  }

  //  private def error(expected: Char, actual: String): ParseError = {
  //    error("'" + expected + "'", actual)
  //  }

  private def error(expected: Char, actual: Char): ParseError = {
    error("'" + expected + "'", "'" + actual + "'")
  }

}

/** Collection of static methods. */
object TextToKore {
  /** Check if the character is among symbol characters.
    *
    * Requires Link To Builder Class.
    * {{{ SymbolChar = [a-zA-Z0-9.@#$%^_-]+ }}}
    */

  def apply(b: Builders): TextToKore = new TextToKore(b)

  def isSymbolChar(c: Char): Boolean = {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') ||
      c == '.' || c == '@' || c == '#' || c == '$' || c == '%' || c == '^' || c == '_' || c == '-' || c == '\\' ||
      c == '`' || c == '''
  }

  //  // SymbolChar = [^[]():]
  //  def isSymbolChar(c: Char): Boolean = {
  //    val i = c.toInt
  //    33 <= i && i <= 126 && // non-white-space characters: from ! to ~ except the following:
  //      i != '[' && i != ']' && i != '(' && i != ')' && i != ':' // && i != '=' && i != ','
  //  }
}
