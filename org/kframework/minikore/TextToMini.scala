package org.kframework.minikore

import org.apache.commons.lang3.StringEscapeUtils
import org.kframework.minikore.MiniKore._


case class ParseError(msg: String) extends Exception



class TextToMini {
  val Scanner = new Scanner()


  def consume(str: String): Unit = {
    Scanner.consumeWhiteSpaces()
    consumeNoLeadingSpaces(str)
  }
  def consumeNoLeadingSpaces(str: String): Unit = {
    for (c <- str) {
      val n = Scanner.nextWithSpaces()
      if (n == c) ()
      else throw error(c, n)
    }
  }

  def error(expected: String, actual: String): ParseError = {
    ParseError(
      "ERROR: " + "Line " + Scanner.lineNum + ": Column " + Scanner.columnNum + ": " +
        "Expected " + expected + ", but " + actual + "\n" +
        Scanner.line + "\n" +
        List.fill(Scanner.columnNum - 1)(' ').mkString + "^"
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

  //////////////////////////////////////////////////////////

  def parse(file: java.io.File): Definition = {
    parse(io.Source.fromFile(file))
    // parse(new java.io.BufferedReader(new java.io.FileReader(file)))
  }

  def parse(src: io.Source): Definition = {
    try {
      Scanner.init(src)
      parseDefinition()
    } finally {
      Scanner.close()
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
    consume("[")
    val att = parseList(parsePattern, ',', ']')
    consume("]")
    att
  }

  // Modules = <EOF> // <empty>
  //         | Module Modules
  def parseModules(modules: Seq[Module]): Seq[Module] = {
    val isEOF =
      try {
        Scanner.putback(Scanner.next()) // check if EOF
        false
      } catch {
        case _: java.io.EOFException => true
        case _: Throwable => ???
      }
    if (isEOF) modules
    else {
      val mod = parseModule()
      parseModules(modules :+ mod)
    }
  }

  // Module = module ModuleName Sentences endmodule Attributes
  def parseModule(): Module = {
    consume("module")
    val name = parseModuleName()
    val sentences = parseSentences(Seq())
    consume("endmodule")
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
    Scanner.next() match {
      case 'i' => consumeNoLeadingSpaces("mport")
        val sen = parseImport()
        parseSentences(sentences :+ sen)
      case 's' => consumeNoLeadingSpaces("yntax")
        val sort = parseSort()
        Scanner.next() match {
          case '[' => Scanner.putback('[')
            val att = parseAttributes()
            val sen = SortDeclaration(sort, att)
            parseSentences(sentences :+ sen)
          case ':' => consumeNoLeadingSpaces(":=")
            val (symbol, args, att) = parseSymbolDeclaration()
            val sen = SymbolDeclaration(sort, symbol, args, att)
            parseSentences(sentences :+ sen)
          case err => throw error("'[' or ':'", err)
        }
      case 'r' => consumeNoLeadingSpaces("ule")
        val sen = parseRule()
        parseSentences(sentences :+ sen)
      case 'a' => consumeNoLeadingSpaces("xiom")
        val sen = parseAxiom()
        parseSentences(sentences :+ sen)
      case 'e' => Scanner.putback('e') // endmodule
        sentences
      case err => throw error("import, syntax, rule, axiom, or endmodule", err)
    }
  }

  // SymbolDeclaration = Symbol ( List{Sort, ',', ')'} ) Attributes
  // Sort = Name
  def parseSymbolDeclaration(): Tuple3[String, Seq[String], Attributes] = {
    val symbol = parseSymbol()
    consume("(")
    val args = parseList(parseSort, ',', ')')
    consume(")")
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
  //         | \Scanner.next ( Pattern )
  //         | \rewrite ( Pattern , Pattern )
  //         | \equal ( Pattern , Pattern )
  def parsePattern(): Pattern = {
    Scanner.next() match {
      case '\\' =>
        val c1 = Scanner.nextWithSpaces()
        val c2 = Scanner.nextWithSpaces()
        (c1, c2) match {
          case ('t', 'r') => consumeNoLeadingSpaces("ue"); consume("("); consume(")")
            True()
          case ('f', 'a') => consumeNoLeadingSpaces("lse"); consume("("); consume(")")
            False()
          case ('a', 'n') => consumeNoLeadingSpaces("d"); consume("(")
            val p1 = parsePattern(); consume(",")
            val p2 = parsePattern(); consume(")")
            And(p1, p2)
          case ('o', 'r') => consume("(")
            val p1 = parsePattern(); consume(",")
            val p2 = parsePattern(); consume(")")
            Or(p1, p2)
          case ('n', 'o') => consumeNoLeadingSpaces("t"); consume("(")
            val p = parsePattern(); consume(")")
            Not(p)
          case ('i', 'm') => consumeNoLeadingSpaces("plies"); consume("(")
            val p1 = parsePattern(); consume(",")
            val p2 = parsePattern(); consume(")")
            Implies(p1, p2)
          case ('e', 'x') => consumeNoLeadingSpaces("ists"); consume("(")
            val v = parseVariable(); consume(",")
            val p = parsePattern(); consume(")")
            Exists(v, p)
          case ('f', 'o') => consumeNoLeadingSpaces("rall"); consume("(")
            val v = parseVariable(); consume(",")
            val p = parsePattern(); consume(")")
            ForAll(v, p)
          case ('n', 'e') => consumeNoLeadingSpaces("xt"); consume("(")
            val p = parsePattern(); consume(")")
            Next(p)
          case ('r', 'e') => consumeNoLeadingSpaces("write"); consume("(")
            val p1 = parsePattern(); consume(",")
            val p2 = parsePattern(); consume(")")
            Rewrite(p1, p2)
          case ('e', 'q') => consumeNoLeadingSpaces("ual"); consume("(")
            val p1 = parsePattern(); consume(",")
            val p2 = parsePattern(); consume(")")
            Equal(p1, p2)
          case err => throw error("\\true, \\false, \\and, \\or, \\not, \\implies, \\exists, \\forall, \\Scanner.next, \\rewrite, or \\equal", err.toString())
        }
      case c => Scanner.putback(c)
        val symbol = parseSymbol() // or parseName()
        Scanner.next() match {
          case ':' => // TODO(Daejun): check if symbol is Name
            val sort = parseSort()
            Variable(symbol, sort)
          case '(' =>
            Scanner.next() match {
              case '"' => Scanner.putback('"')
                val value = parseString()
                consume(")")
                DomainValue(symbol, value)
              case c => Scanner.putback(c)
                val args = parseList(parsePattern, ',', ')')
                consume(")")
                Application(symbol, args)
            }
          case err => throw error("':' or '('", err)
        }
    }
  }

  // Variable = Name : Sort
  def parseVariable(): Variable = {
    val name = parseName()
    consume(":")
    val sort = parseSort()
    Variable(name, sort)
  }

  //////////////////////////////////////////////////////////

  // String = " <char> "
  def parseString(): String = {
    def loop(s: StringBuilder): String = {
      Scanner.nextWithSpaces() match {
        case '"' =>
          s.toString()
        case '\\' =>
          val c = Scanner.nextWithSpaces()
          val s1 = StringEscapeUtils.unescapeJava("\\" + c)
          s ++= s1; loop(s)
        case c =>
          s += c; loop(s)
      }
    }
    Scanner.next() match {
      case '"' => loop(new StringBuilder())
      case err => throw error('"', err)
    }
  }

  // ModuleName = [A-Z][A-Z-]*
  def parseModuleName(): String = {
    def loop(s: StringBuilder): String = {
      Scanner.nextWithSpaces() match {
        case c if ('A' <= c && c <= 'Z') || c == '-'  =>
          s += c; loop(s)
        case c => Scanner.putback(c)
          s.toString()
      }
    }
    Scanner.next() match {
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
//      Scanner.nextWithSpaces() match {
//        case c if ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || c == '@' || c == '-' =>
//          s += c; loop(s)
//        case c => Scanner.putback(c)
//          s.toString()
//      }
//    }
//    Scanner.next() match {
//      case '`' => Scanner.putback('`')
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
      Scanner.nextWithSpaces() match {
        case c if isSymbolChar(c) =>
          s += c; loop(s)
        case c => Scanner.putback(c)
          s.toString()
      }
    }
    Scanner.next() match {
      case '`' => Scanner.putback('`')
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
      Scanner.nextWithSpaces() match {
        case '`' =>
          s.toString()
        case c =>
          s += c; loop(s)
      }
    }
    Scanner.next() match {
      case '`' =>
        loop(new StringBuilder())
      case err => throw error('`', err)
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
      Scanner.next() match {
        case c if c == endsWith => Scanner.putback(c)
          lst
        case c if c == sep =>
          val elem = parseElem()
          parseList2(lst :+ elem)
        case err => throw error("'" + endsWith + "' or '" + sep + "'", err)
      }
    }
    Scanner.next() match {
      case c if c == endsWith => Scanner.putback(c)
        Seq()
      case c => Scanner.putback(c)
        val elem = parseElem()
        parseList2(Seq(elem))
    }
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
