package org.kframework.minikore

import org.apache.commons.lang3.StringEscapeUtils
import org.kframework.minikore.MiniKore._

case class ParseError(msg: String) extends Exception

class TextToMini {
  val scanner = new Scanner()

  def parse(file: java.io.File): Definition = {
    parse(io.Source.fromFile(file))
  }

  def parse(src: io.Source): Definition = {
    try {
      scanner.init(src)
      parseDefinition()
    } finally {
      scanner.close()
    }
  }

  // Definition = Attributes Modules
  def parseDefinition(): Definition = {
    val att = parseAttributes()
    val modules = parseModules(Seq())
    Definition(modules, att)
  }

  // Attributes = [ List{Pattern, ',', ']'} ]
  def parseAttributes(): Attributes = {
    consumeWithLeadingWhitespaces("[")
    val att = parseList(parsePattern, ',', ']')
    consumeWithLeadingWhitespaces("]")
    att
  }

  // Modules = <EOF> // <empty>
  //         | Module Modules
  def parseModules(modules: Seq[Module]): Seq[Module] = {
    if (scanner.isEOF()) modules
    else {
      val mod = parseModule()
      parseModules(modules :+ mod)
    }
  }

  // Module = module ModuleName Sentences endmodule Attributes
  def parseModule(): Module = {
    consumeWithLeadingWhitespaces("module")
    val name = parseModuleName()
    val sentences = parseSentences(Seq())
    consumeWithLeadingWhitespaces("endmodule")
    val att = parseAttributes()
    Module(name, sentences, att)
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
  def parseSentences(sentences: Seq[Sentence]): Seq[Sentence] = {
    scanner.nextWithSkippingWhitespaces() match {
      case 'i' => consume("mport")
        val sen = parseImport()
        parseSentences(sentences :+ sen)
      case 's' => consume("yntax")
        val sort = parseSort()
        scanner.nextWithSkippingWhitespaces() match {
          case '[' => scanner.putback('[')
            val att = parseAttributes()
            val sen = SortDeclaration(sort, att)
            parseSentences(sentences :+ sen)
          case ':' => consume(":=")
            val (symbol, args, att) = parseSymbolDeclaration()
            val sen = SymbolDeclaration(sort, symbol, args, att)
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
  def parseSymbolDeclaration(): Tuple3[String, Seq[String], Attributes] = {
    val symbol = parseSymbol()
    consumeWithLeadingWhitespaces("(")
    val args = parseList(parseSort, ',', ')')
    consumeWithLeadingWhitespaces(")")
    val att = parseAttributes()
    (symbol, args, att)
  }

  // Import = ModuleName Attributes
  def parseImport(): Import = {
    val name = parseModuleName()
    val att = parseAttributes()
    Import(name, att)
  }

  // Rule = Pattern Attributes
  def parseRule(): Rule = {
    val pattern = parsePattern()
    val att = parseAttributes()
    Rule(pattern, att)
  }

  // Axiom = Pattern Attributes
  def parseAxiom(): Axiom = {
    val pattern = parsePattern()
    val att = parseAttributes()
    Axiom(pattern, att)
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
  def parsePattern(): Pattern = {
    scanner.nextWithSkippingWhitespaces() match {
      case '\\' =>
        val c1 = scanner.next()
        val c2 = scanner.next()
        (c1, c2) match {
          case ('t', 'r') => consume("ue"); consumeWithLeadingWhitespaces("("); consumeWithLeadingWhitespaces(")")
            True()
          case ('f', 'a') => consume("lse"); consumeWithLeadingWhitespaces("("); consumeWithLeadingWhitespaces(")")
            False()
          case ('a', 'n') => consume("d"); consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern(); consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern(); consumeWithLeadingWhitespaces(")")
            And(p1, p2)
          case ('o', 'r') => consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern(); consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern(); consumeWithLeadingWhitespaces(")")
            Or(p1, p2)
          case ('n', 'o') => consume("t"); consumeWithLeadingWhitespaces("(")
            val p = parsePattern(); consumeWithLeadingWhitespaces(")")
            Not(p)
          case ('i', 'm') => consume("plies"); consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern(); consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern(); consumeWithLeadingWhitespaces(")")
            Implies(p1, p2)
          case ('e', 'x') => consume("ists"); consumeWithLeadingWhitespaces("(")
            val v = parseVariable(); consumeWithLeadingWhitespaces(",")
            val p = parsePattern(); consumeWithLeadingWhitespaces(")")
            Exists(v, p)
          case ('f', 'o') => consume("rall"); consumeWithLeadingWhitespaces("(")
            val v = parseVariable(); consumeWithLeadingWhitespaces(",")
            val p = parsePattern(); consumeWithLeadingWhitespaces(")")
            ForAll(v, p)
          case ('n', 'e') => consume("xt"); consumeWithLeadingWhitespaces("(")
            val p = parsePattern(); consumeWithLeadingWhitespaces(")")
            Next(p)
          case ('r', 'e') => consume("write"); consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern(); consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern(); consumeWithLeadingWhitespaces(")")
            Rewrite(p1, p2)
          case ('e', 'q') => consume("ual"); consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern(); consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern(); consumeWithLeadingWhitespaces(")")
            Equal(p1, p2)
          case (err1, err2) => throw error("\\true, \\false, \\and, \\or, \\not, \\implies, \\exists, \\forall, \\next, \\rewrite, or \\equal", "'" + err1 + err2 + "'")
        }
      case c => scanner.putback(c)
        val symbol = parseSymbol() // or parseName()
        scanner.nextWithSkippingWhitespaces() match {
          case ':' => // TODO(Daejun): check if symbol is Name
            val sort = parseSort()
            Variable(symbol, sort)
          case '(' =>
            scanner.nextWithSkippingWhitespaces() match {
              case '"' => scanner.putback('"')
                val value = parseString()
                consumeWithLeadingWhitespaces(")")
                DomainValue(symbol, value)
              case c => scanner.putback(c)
                val args = parseList(parsePattern, ',', ')')
                consumeWithLeadingWhitespaces(")")
                Application(symbol, args)
            }
          case err => throw error("':' or '('", err)
        }
    }
  }

  // Variable = Name : Sort
  def parseVariable(): Variable = {
    val name = parseName()
    consumeWithLeadingWhitespaces(":")
    val sort = parseSort()
    Variable(name, sort)
  }

  //////////////////////////////////////////////////////////

  // String = " <char> "
  def parseString(): String = {
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

  // ModuleName = [A-Z][A-Z-]*
  def parseModuleName(): String = {
    def loop(s: StringBuilder): String = {
      scanner.next() match {
        case c if ('A' <= c && c <= 'Z') || c == '-'  =>
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

  def isModuleNameStart(c: Char): Boolean = {
    'A' <= c && c <= 'Z'
  }

  // TODO(Daejun): double check Sort, Name, Symbol

  // Sort = Name
  def parseSort(): String = parseName() // TODO(Daejun): directly alias function name instead of delegation?

  // Name = Symbol
  def parseName(): String = parseSymbol()

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
  def parseSymbol(): String = {
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

  def isSymbolChar(c: Char): Boolean = TextToMini.isSymbolChar(c) // TODO(Daejun): more efficient way?

  // EscapedSymbol = ` [^`] `
  def parseEscapedSymbol(): String = {
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
  def parseList[T](parseElem: () => T, sep: Char, endsWith: Char): Seq[T] = {
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

  def consumeWithLeadingWhitespaces(str: String): Unit = {
    scanner.skipWhitespaces()
    consume(str)
  }

  def consume(str: String): Unit = {
    for (c <- str) {
      val n = scanner.next()
      if (n == c) ()
      else throw error(c, n)
    }
  }

  //////////////////////////////////////////////////////////

  def error(expected: String, actual: String): ParseError = {
    ParseError(
      "ERROR: " + "Line " + scanner.lineNum + ": Column " + scanner.columnNum + ": " +
        "Expected " + expected + ", but " + StringEscapeUtils.escapeJava(actual) + System.lineSeparator() +
        scanner.line + System.lineSeparator() +
        List.fill(scanner.columnNum - 1)(' ').mkString + "^"
    )
  }

  def error(expected: String, actual: Char): ParseError = {
    error(expected, "'" + actual + "'")
  }

  def error(expected: Char, actual: String): ParseError = {
    error("'" + expected + "'", actual)
  }

  def error(expected: Char, actual: Char): ParseError = {
    error("'" + expected + "'", "'" + actual + "'")
  }

}

object TextToMini {
  // SymbolChar = [a-zA-Z0-9.@#$%^_-]+
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
