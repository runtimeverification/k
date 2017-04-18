package org.kframework.kore.parser

import org.apache.commons.lang3.StringEscapeUtils
import org.kframework.kore.interfaces.Builders
import org.kframework.kore.interfaces.Kore._

/** Parsing error exception. */
case class ParseError(msg: String) extends Exception(msg) // ParseError.msg eq Exception.detailMessage, i.e., msg() == getMessage()

/** A parser for [[org.kframework.kore.interfaces.Kore.Pattern]].
  *
  * @constructor Creates a new parser.
  */
class TextToKore(b: Builders) {
  private val scanner = new Scanner()

  /** Parses the file and returns [[org.kframework.kore.interfaces.Kore.Definition]]. */
  @throws(classOf[ParseError])
  def parse(file: java.io.File): Definition = {
    parse(io.Source.fromFile(file))
  }

  /** Parses from the stream and returns [[org.kframework.kore.interfaces.Kore.Definition]]. */
  @throws(classOf[ParseError])
  def parse(src: io.Source): Definition = {
    try {
      scanner.init(src)
      parseDefinition()
    } catch {
      case _: java.io.EOFException => throw ParseError("ERROR: Unexpected end of file while parsing")
      case exc: ParseError => throw exc
      case exc: Throwable => throw ParseError("ERROR: Unexpected error while parsing: " + exc.toString) // shouldn't be reachable
    } finally {
      scanner.close()
    }
  }

  // Definition = Attributes Modules
  private def parseDefinition(): Definition = {
    val att = parseAttributes()
    val modules = parseModules(Seq())
    b.Definition(modules, att)
  }

  // Attributes = [ List{Pattern, ',', ']'} ]
  private def parseAttributes(): Attributes = {
    consumeWithLeadingWhitespaces("[")
    val att = parseList(parsePattern, ',', ']')
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
  // Sentence = import Import
  //          | syntax Sort SortOrSymbolDeclaration
  //          | rule Rule
  //          | axiom Axiom
  // SortOrSymbolDeclaration = Attributes
  //                         | ::= SymbolDeclaration
  // Sort = Name
  private def parseSentences(sentences: Seq[Sentence]): Seq[Sentence] = {
    scanner.nextWithSkippingWhitespaces() match {
      case 'i' => consume("mport")
        val sen = parseImport()
        parseSentences(sentences :+ sen)
      case 's' => consume("yntax")
        val sort = parseSort()
        scanner.nextWithSkippingWhitespaces() match {
          case '[' => scanner.putback('[')
            val att = parseAttributes()
            val sen = b.SortDeclaration(b.Sort(sort), att)
            parseSentences(sentences :+ sen)
          case ':' => consume(":=")
            val (symbol, args, att) = parseSymbolDeclaration()
            val sen = b.SymbolDeclaration(b.Sort(sort), b.Symbol(symbol), args, att)
            parseSentences(sentences :+ sen)
          case err => throw error("'[' or ':'", err)
        }
      case 'r' => consume("ule")
        val sen = parseRule()
        parseSentences(sentences :+ sen)
      case 'a' => consume("xiom")
        val sen = parseAxiom()
        parseSentences(sentences :+ sen)
      case 'e' => scanner.putback('e') // endmodule
        sentences
      case err => throw error("import, syntax, rule, axiom, or endmodule", err)
    }
  }

  // SymbolDeclaration = Symbol ( List{Sort, ',', ')'} ) Attributes
  // Sort = Name
  private def parseSymbolDeclaration(): Tuple3[String, Seq[Sort], Attributes] = {
    val symbol = parseSymbol()
    consumeWithLeadingWhitespaces("(")
    val args = parseList(parseSort, ',', ')')
    consumeWithLeadingWhitespaces(")")
    val att = parseAttributes()
    (symbol, args.map(b.Sort), att)
  }

  // Import = ModuleName Attributes
  private def parseImport(): Import = {
    val name = parseModuleName()
    val att = parseAttributes()
    b.Import(b.ModuleName(name), att)
  }

  // Rule = Pattern Attributes
  private def parseRule(): Rule = {
    val pattern = parsePattern()
    val att = parseAttributes()
    b.Rule(pattern, att)
  }

  // Axiom = Pattern Attributes
  private def parseAxiom(): Axiom = {
    val pattern = parsePattern()
    val att = parseAttributes()
    b.Axiom(pattern, att)
  }

  // Pattern = Variable
  //         | Symbol ( List{Pattern, ',', ')'} )
  //         | Symbol ( String )
  //         | \true ( )
  //         | \false ( )
  //         | \and ( Pattern , Pattern )
  //         | \or ( Pattern , Pattern )
  //         | \not ( Pattern )
  //         | \implies ( Pattern , Pattern )
  //         | \exists ( Variable , Pattern )
  //         | \forall ( Variable , Pattern )
  //         | \next ( Pattern )
  //         | \rewrite ( Pattern , Pattern )
  //         | \equal ( Pattern , Pattern )
  private def parsePattern(): Pattern = {
    scanner.nextWithSkippingWhitespaces() match {
      case '\\' =>
        val c1 = scanner.next()
        val c2 = scanner.next()
        (c1, c2) match {
          case ('t', 'o') => consume("p"); consumeWithLeadingWhitespaces("("); consumeWithLeadingWhitespaces(")")
            b.Top()
          case ('b', 'o') => consume("ttom"); consumeWithLeadingWhitespaces("("); consumeWithLeadingWhitespaces(")")
            b.Bottom()
          case ('a', 'n') => consume("d"); consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern(); consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern(); consumeWithLeadingWhitespaces(")")
            b.And(p1, p2)
          case ('o', 'r') => consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern(); consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern(); consumeWithLeadingWhitespaces(")")
            b.Or(p1, p2)
          case ('n', 'o') => consume("t"); consumeWithLeadingWhitespaces("(")
            val p = parsePattern(); consumeWithLeadingWhitespaces(")")
            b.Not(p)
          case ('i', 'm') => consume("plies"); consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern(); consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern(); consumeWithLeadingWhitespaces(")")
            b.Implies(p1, p2)
          case ('e', 'x') => consume("ists"); consumeWithLeadingWhitespaces("(")
            val v = parseVariable(); consumeWithLeadingWhitespaces(",")
            val p = parsePattern(); consumeWithLeadingWhitespaces(")")
            b.Exists(v, p)
          case ('f', 'o') => consume("rall"); consumeWithLeadingWhitespaces("(")
            val v = parseVariable(); consumeWithLeadingWhitespaces(",")
            val p = parsePattern(); consumeWithLeadingWhitespaces(")")
            b.ForAll(v, p)
          case ('n', 'e') => consume("xt"); consumeWithLeadingWhitespaces("(")
            val p = parsePattern(); consumeWithLeadingWhitespaces(")")
            b.Next(p)
          case ('r', 'e') => consume("write"); consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern(); consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern(); consumeWithLeadingWhitespaces(")")
            b.Rewrite(p1, p2)
          case ('e', 'q') => consume("uals"); consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern(); consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern(); consumeWithLeadingWhitespaces(")")
            b.Equals(p1, p2)
          case (err1, err2) => throw error("\\top, \\bottom, \\and, \\or, \\not, \\implies, \\exists, \\forall, \\next, \\rewrite, or \\equals",
                                           "'\\" + err1 + err2 + "'")
        }
      case c => scanner.putback(c)
        val symbol = parseSymbol() // or parseName()
        scanner.nextWithSkippingWhitespaces() match {
          case ':' => // TODO(Daejun): check if symbol is Name
            val sort = parseSort()
            b.Variable(b.Name(symbol), b.Sort(sort))
          case '(' =>
            scanner.nextWithSkippingWhitespaces() match {
              case '"' => scanner.putback('"')
                val value = parseString()
                consumeWithLeadingWhitespaces(")")
                b.DomainValue(b.Symbol(symbol), b.Value(value))
              case c => scanner.putback(c)
                val args = parseList(parsePattern, ',', ')')
                consumeWithLeadingWhitespaces(")")
                b.Application(b.Symbol(symbol), args)
            }
          case err => throw error("':' or '('", err)
        }
    }
  }

  // Variable = Name : Sort
  private def parseVariable(): Variable = {
    val nameStr = parseName()
    consumeWithLeadingWhitespaces(":")
    val sort = parseSort()
    b.Variable(b.Name(nameStr), b.Sort(sort))
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
          s ++= s1; loop(s)
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
        case c if ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || c == '-'  =>
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

  // TODO(Daejun): double check Sort, Name, Symbol

  // Sort = Name
  private def parseSort(): String = parseName() // TODO(Daejun): directly alias function name instead of delegation?

  // Name = Symbol
  private def parseName(): String = parseSymbol()

//  // Name = [A-Z][a-zA-Z@-]*  // for Sort or VariableName
//  //      | EscapedSymbol
//  def parseName(): String = {
//    def loop(s: StringBuilder): String = {
//      scanner.next() match {
//        case c if ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || c == '@' || c == '-' =>
//          s += c; loop(s)
//        case c => scanner.putback(c)
//          s.toString()
//      }
//    }
//    scanner.nextWithSkippingWhitespaces() match {
//      case '`' => scanner.putback('`')
//        parseEscapedSymbol()
//      case c if isNameStart(c) =>
//        loop(new StringBuilder(c.toString))
//      case err => throw error("<Name>", err)
//    }
//  }
//  def isNameStart(c: Char): Boolean = {
//    'A' <= c && c <= 'Z'
//  }

  // Symbol = SymbolChar+
  //        | EscapedSymbol
  private def parseSymbol(): String = {
    def loop(s: StringBuilder): String = {
      scanner.next() match {
        case c if isSymbolChar(c) =>
          s += c; loop(s)
        case c => scanner.putback(c)
          s.toString()
      }
    }
    scanner.nextWithSkippingWhitespaces() match {
      case '`' => scanner.putback('`')
        parseEscapedSymbol()
      case c if isSymbolChar(c) =>
        loop(new StringBuilder(c.toString))
      case err => throw error("<Symbol>", err)
    }
  }

  private def isSymbolChar(c: Char): Boolean = TextToKore.isSymbolChar(c) // TODO(Daejun): more efficient way?

  // EscapedSymbol = ` [^`] `
  private def parseEscapedSymbol(): String = {
    def loop(s: StringBuilder): String = {
      scanner.next() match {
        case '`' =>
          s.toString()
        case c =>
          s += c; loop(s)
      }
    }
    scanner.nextWithSkippingWhitespaces() match {
      case '`' =>
        loop(new StringBuilder())
      case err => throw error('`', err) // shouldn't be reachable
    }
  }

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
      c == '.' || c == '@' || c == '#' || c == '$' || c == '%' || c == '^' || c == '_' || c == '-'
  }
//  // SymbolChar = [^[]():]
//  def isSymbolChar(c: Char): Boolean = {
//    val i = c.toInt
//    33 <= i && i <= 126 && // non-white-space characters: from ! to ~ except the following:
//      i != '[' && i != ']' && i != '(' && i != ')' && i != ':' // && i != '=' && i != ','
//  }
}
