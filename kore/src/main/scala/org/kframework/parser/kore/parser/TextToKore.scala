package org.kframework.parser.kore.parser

import org.kframework.parser.kore._
import org.kframework.parser.kore
import org.kframework.parser.kore.implementation.DefaultBuilders
import org.kframework.utils.StringUtil

/** Parsing error exception. */
case class ParseError(msg: String) extends Exception(msg) { // ParseError.msg eq Exception.detailMessage, i.e., msg() == getMessage()
  def this(message: String, cause: Throwable) {
    this(message)
    initCause(cause)
  }
}

/** A parser for [[kore.Pattern]].
  *
  * @constructor Creates a new parser.
  */
class TextToKore(b: Builders = DefaultBuilders) {

  def this() {
    this(DefaultBuilders)
  }

  private val scanner = new Scanner()

  /**
    * ParsingLevel ::= None        // both meta-level and object-level are allowed
    *                | Some(true)  // only accept meta-level
    *                | Some(false) // only accept object-level
    */

  private type ParsingLevel = Option[Boolean]

  private val both: ParsingLevel = None

  private val meta: ParsingLevel = Some(true)

  private val objt: ParsingLevel = Some(false)

  // Whenever a syntactic category is parsed, its parsing level (either object or meta) is
  // stored in previousParsingLevel.
  // Recall that Identifier is the only lexicon syntactic category that decides if a syntactic category
  // (such as Sort or Variable) is object-level or meta-level.
  // Therefore, [[parseId]] is the only method that directly modifies previousParsingLevel.
  private var previousParsingLevel: ParsingLevel = both

  /** Parses the file and returns [[kore.Definition]]. */
  @throws(classOf[ParseError])
  def parse(file: java.io.File): Definition = {
    parse(io.Source.fromFile(file))
  }

  /** Parses the file and returns [[kore.Pattern]]. */
  @throws(classOf[ParseError])
  def parsePattern(file: java.io.File): Pattern = {
    parsePattern(io.Source.fromFile(file))
  }

  /** Parses the file and returns [[kore.Pattern]]. */
  @throws(classOf[ParseError])
  def parsePattern(str: String): Pattern = {
    parsePattern(io.Source.fromString(str))
  }

  /** Parses from the stream and returns [[kore.Definition]]. */
  @throws(classOf[ParseError])
  def parse(src: io.Source): Definition = {
    try {
      scanner.init(src)
      parseDefinition()
    } catch {
      case e: java.io.EOFException => throw new ParseError("ERROR: Unexpected end of file while parsing", e)
      case exc: ParseError => throw exc
      case exc: Throwable => throw new ParseError("ERROR: Unexpected error while parsing: " + exc.getMessage, exc) // shouldn't be reachable
    } finally {
      scanner.close()
    }
  }

  /** Parses from the stream and returns [[kore.Definition]]. */
  @throws(classOf[ParseError])
  def parsePattern(src: io.Source): Pattern = {
    try {
      scanner.init(src)
      parsePattern()
    } catch {
      case e: java.io.EOFException => throw new ParseError("ERROR: Unexpected end of file while parsing", e)
      case exc: ParseError => throw exc
      case exc: Throwable => throw new ParseError("ERROR: Unexpected error while parsing: " + exc.getMessage, exc) // shouldn't be reachable
    } finally {
      scanner.close()
    }
  }

  /** Read from the stream and return a canonical form [[String]],
    * in which all consecutive whitespaces are deleted.
    * FIXME:: should return a canonical form [[String]] in which all
    *         consecutive whitespaces are replaced by ' '
    * Mainly used for testing. */
  @throws(classOf[java.io.IOException])
  def canonicalString(file: java.io.File): String = {
    canonicalString(io.Source.fromFile(file))
  }

  @throws(classOf[java.io.IOException])
  def canonicalString(s: String): String = {
    canonicalString(io.Source.fromString(s))
  }

  @throws(classOf[java.io.IOException])
  def canonicalString(src: io.Source): String = {
    def loop(s: StringBuilder): String = {
      if (scanner.isEOF()) {
        return s.toString()
      }
      else {
        s += scanner.next() // s must be a nonwhitespace character
        loop(s)             // tail recursive
      }
    }
    try {
      scanner.init(src)
      loop(new StringBuilder(""))
    }
    catch {
      case e: java.io.EOFException => throw e
    }
  }

  // Definition = Attributes Module
  private def parseDefinition(): Definition = {
    val att = parseAttributes()
    val modules = parseModules()
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
  // private def parseModules(modules: Seq[Module]): Seq[Module] = {
  //   if (scanner.isEOF()) modules
  //   else {
  //     val mod = parseModule()
  //     parseModules(modules :+ mod)
  //   }
  // }

  // Module = module ModuleName Declarations endmodule Attributes
  private def parseModule(): Module = {
    consumeWithLeadingWhitespaces("module")
    val name = parseId(parsingLevel = objt)
    val decls = parseDeclarations(Seq()).reverse
    consumeWithLeadingWhitespaces("endmodule")
    val att = parseAttributes()
    b.Module(name, decls, att)
  }

  private def parseModules() : Seq[Module] = {
    var ms = Seq.empty[Module]
    while(!scanner.isEOF()) {
      val leading_char = scanner.nextWithSkippingWhitespaces()
      if (leading_char == 'm') { // a module starts
        scanner.putback('m')
        val m = parseModule()
        ms = ms :+ m
      }
      else
        throw error('m', leading_char)
    }
    ms
  }

  // Declarations = <lookahead>(e) // <empty>
  //              | Declaration Declarations
  // Declaration = sort { SortVariableList } Sort Attributes
  //             | symbol Symbol ( SortList ) : Sort Attributes
  //             | alias Alias ( SortList ) : Sort Attributes
  //             | axiom { SortVariableList } Axiom
  //             | import Id Attributes
  private def parseDeclarations(decls: Seq[Declaration]): Seq[Declaration] = {
    val c1 = scanner.nextWithSkippingWhitespaces()
    if (c1 == 'e') { // endmodule
      scanner.putback('e')
      decls
    }
    else {
      val c2 = scanner.nextWithSkippingWhitespaces()
      (c1, c2) match {
         case ('i', 'm') => // import
           consume("port")
           val nameStr = parseId()
           val att = parseAttributes()
           val decl = b.Import(nameStr, att)
           parseDeclarations(decl +: decls)
        case ('s', 'o') => // sort declaration
          consume("rt")
          val ctr = parseId(parsingLevel = objt)
          consumeWithLeadingWhitespaces("{")
          val params = parseList(() => parseSortVariable(parsingLevel = objt), ',', '}')
          consumeWithLeadingWhitespaces("}")
          val att = parseAttributes()
          val decl = b.SortDeclaration(params, b.CompoundSort(ctr, params), att)
          parseDeclarations(decl +: decls)
        case ('s', 'y') => // symbol declaration
          consume("mbol")
          val ctr = parseId() // previousParsingLevel is set here
          consumeWithLeadingWhitespaces("{")
          val params = parseList(() => parseSortVariable(parsingLevel = previousParsingLevel), ',', '}')
          consumeWithLeadingWhitespaces("}")
          val symbol = b.Symbol(ctr, params)
          consumeWithLeadingWhitespaces("(")
          val argSorts = parseList(() => parseSort(parsingLevel = previousParsingLevel), ',', ')')
          consumeWithLeadingWhitespaces(")")
          consumeWithLeadingWhitespaces(":")
          val returnSort = parseSort(parsingLevel = previousParsingLevel)
          val att = parseAttributes()
          val decl = b.SymbolDeclaration(symbol, argSorts, returnSort, att)
          parseDeclarations(decl +: decls)
        case ('h', 'o') => // hook-sort or hook-symbol declaration
          consume("oked-")
          val c1 = scanner.next()
          val c2 = scanner.next()
          (c1, c2) match {
            case ('s', 'o') => // hook-sort
              consume("rt")
              val ctr = parseId(parsingLevel = objt)
              consumeWithLeadingWhitespaces("{")
              val params = parseList(() => parseSortVariable(parsingLevel = objt), ',', '}')
              consumeWithLeadingWhitespaces("}")
              val att = parseAttributes()
              val decl = b.HookSortDeclaration(params, b.CompoundSort(ctr, params), att)
              parseDeclarations(decl +: decls)
            case ('s', 'y') => // hook-symbol
              consume("mbol")
              val ctr = parseId() // previousParsingLevel is set here
              consumeWithLeadingWhitespaces("{")
              val params = parseList(() => parseSortVariable(parsingLevel = previousParsingLevel), ',', '}')
              consumeWithLeadingWhitespaces("}")
              val symbol = b.Symbol(ctr, params)
              consumeWithLeadingWhitespaces("(")
              val argSorts = parseList(() => parseSort(parsingLevel = previousParsingLevel), ',', ')')
              consumeWithLeadingWhitespaces(")")
              consumeWithLeadingWhitespaces(":")
              val returnSort = parseSort(parsingLevel = previousParsingLevel)
              val att = parseAttributes()
              val decl = b.HookSymbolDeclaration(symbol, argSorts, returnSort, att)
              parseDeclarations(decl +: decls)
            case (e1, e2) => // error
              throw error("sort, symbol", e1)
          }
        case ('a', 'l') => // alias declaration
          consume("ias")
          val ctr = parseId() // previousParsingLevel is set here
          consumeWithLeadingWhitespaces("{")
          val params = parseList(() => parseSortVariable(parsingLevel = previousParsingLevel), ',', '}')
          consumeWithLeadingWhitespaces("}")
          val alias = b.Alias(ctr, params)
          consumeWithLeadingWhitespaces("(")
          val argSorts = parseList(() => parseSort(parsingLevel = previousParsingLevel), ',', ')')
          consumeWithLeadingWhitespaces(")")
          consumeWithLeadingWhitespaces(":")
          val returnSort = parseSort(parsingLevel = previousParsingLevel)
          consumeWithLeadingWhitespaces("where")
          val leftPattern = parsePattern()
          consumeWithLeadingWhitespaces(":=")
          val rightPattern = parsePattern()
          val att = parseAttributes()
          val decl = b.AliasDeclaration(alias, argSorts, returnSort, leftPattern, rightPattern, att)
          parseDeclarations(decl +: decls)
        case ('a', 'x') => // axiom declaration
          consume("iom")
          consumeWithLeadingWhitespaces("{")
          val params = parseList(() => parseSortVariable(parsingLevel = both), ',', '}')
          consumeWithLeadingWhitespaces("}")
          val pattern = parsePattern()
          val att = parseAttributes()
          val decl = b.AxiomDeclaration(params, pattern, att)
          parseDeclarations(decl +: decls)
        case  ('c', 'l') => // claim declaration
          consume("aim")
          consumeWithLeadingWhitespaces("{")
          val params = parseList(() => parseSortVariable(parsingLevel = both), ',', '}')
          consumeWithLeadingWhitespaces("}")
          val pattern = parsePattern()
          val att = parseAttributes()
          val decl = b.ClaimDeclaration(params, pattern, att)
          parseDeclarations(decl +: decls)
         case (e1, e2) =>
          throw error("sort, symbol, alias, axiom", e1)
      }
    }
  }


  // Import = ModuleName Attributes
  // private def parseImport(): Declaration = {
  //   val name = parseModuleName()
  //   val att = parseAttributes()
  //   b.Import(b.ModuleName(name), att)
  // }

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
  //         | \ceil { Sort , Sort } ( Pattern )
  //         | \floor { Sort , Sort } ( Pattern )
  //         | \equal  { Sort , Sort } ( Pattern , Pattern )
  //         | \mem { Sort , Sort } ( Variable , Pattern )
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
          // TODO:: Read two chars only if needed.
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
          // case ('n', 'e') => // next
          //   consume("xt")
          //   consumeWithLeadingWhitespaces("{")
          //   val s = parseSort()
          //   consumeWithLeadingWhitespaces("}")
          //   consumeWithLeadingWhitespaces("(")
          //   val p = parsePattern()
          //   consumeWithLeadingWhitespaces(")")
          //   b.Next(s, p)
          case ('r', 'e') => // rewrites
            consume("writes")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort()
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern()
            consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Rewrites(s, p1, p2)
          case ('c', 'e') => // ceil
            consume("il")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort() // previousParsingLevel is set here
            consumeWithLeadingWhitespaces(",")
            val rs = parseSort(parsingLevel = previousParsingLevel)
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Ceil(s, rs, p)
          case ('f', 'l') => // floor
            consume("oor")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort() // previousParsingLevel is set here
            consumeWithLeadingWhitespaces(",")
            val rs = parseSort(parsingLevel = previousParsingLevel)
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Floor(s, rs, p)
          case ('e', 'q') => // equals
            consume("uals")
            consumeWithLeadingWhitespaces("{")
            val s = parseSort() // previousParsingLevel is set here
            consumeWithLeadingWhitespaces(",")
            val rs = parseSort(parsingLevel = previousParsingLevel)
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p1 = parsePattern()
            consumeWithLeadingWhitespaces(",")
            val p2 = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Equals(s, rs, p1, p2)
          case ('i', 'n') => // in
            consumeWithLeadingWhitespaces("{")
            val s = parseSort() // previousParsingLevel is set here
            consumeWithLeadingWhitespaces(",")
            val rs = parseSort(parsingLevel = previousParsingLevel)
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val p = parsePattern()
            consumeWithLeadingWhitespaces(",")
            val q = parsePattern()
            consumeWithLeadingWhitespaces(")")
            b.Mem(s, rs, p, q)
          case ('d', 'v') => // dv
            consumeWithLeadingWhitespaces("{")
            val s = parseSort() // previousParsingLevel is set here
            consumeWithLeadingWhitespaces("}")
            consumeWithLeadingWhitespaces("(")
            val str = parseString()
            consumeWithLeadingWhitespaces(")")
            b.DomainValue(s, str)
          // case ('s', 'u') => // subset
          //   consume("bset")
          //   consumeWithLeadingWhitespaces("{")
          //   val s = parseSort()
          //   consumeWithLeadingWhitespaces(",")
          //   val rs = parseSort()
          //   consumeWithLeadingWhitespaces("}")
          //   consumeWithLeadingWhitespaces("(")
          //   val p1 = parsePattern()
          //   consumeWithLeadingWhitespaces(",")
          //   val p2 = parsePattern()
          //   consumeWithLeadingWhitespaces(")")
          //   b.Subset(s, rs, p1, p2)
          // case ('d', 'o') => // domainvalue
          //   consume("mainvalue")
          //   consumeWithLeadingWhitespaces("(")
          //   val sortStr = parseString()
          //   consumeWithLeadingWhitespaces(",")
          //   val valueStr = parseString()
          //   consumeWithLeadingWhitespaces(")")
          //   b.DomainValue(sortStr, valueStr)
          case (err1, err2) =>
            val known = Seq(
              "\\top", "\\bottom", "\\and", "\\or", "\\implies",
              "\\iff", "\\exists", "\\forall", "\\ceil", "\\floor",
              "\\equals", "\\mem")
            throw error(known.mkString(","), "'\\" + err1 + err2 + "'")
        }
      case '@' => // set variable
        val id = parseId()
        scanner.nextWithSkippingWhitespaces() match {
          case ':' => // set variable
            val sort = parseSort(parsingLevel = previousParsingLevel)
            b.SetVariable("@" + id, sort)
          case err =>
            throw error("':'", err)
        }
      case c => // variable or application
        scanner.putback(c)
        val id = parseId() // previousParsingLevel is set here
        scanner.nextWithSkippingWhitespaces() match {
          case ':' => // variable
            val sort = parseSort(parsingLevel = previousParsingLevel)
            b.Variable(id, sort)
          case '{' => // application: symbol or alias
            val params = parseList(() => parseSort(parsingLevel = previousParsingLevel), ',', '}')
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
    val name = parseId() // previousParsingLevel is set here
    consumeWithLeadingWhitespaces(":")
    val sort = parseSort(parsingLevel = previousParsingLevel)
    b.Variable(name, sort)
  }

  //////////////////////////////////////////////////////////

  private def parseString(): String = {
    def loop(s: StringBuilder): String = {
      val c = scanner.next()
      s += c;
      c match {
         case '\\' =>
           // Always grab one character after the escaping backslash. We do not
           // need to grab the entire escape sequence now, because actual
           // unquoting does not happen until we have the entire string literal;
           // this is only to prevent parsing the final quote prematurely.
           s += scanner.next();
           loop(s)
         case '"' =>
           StringUtil.unquoteKString(s.toString())
         case c =>
           loop(s)
      }
    }

    scanner.nextWithSkippingWhitespaces() match {
      case '"' =>
        val s = new StringBuilder()
        s += '"';
        loop(s)
      case err => throw error('"', err) // shouldn't be reachable
    }
  }


  // Sort = SortVariable | Name { List{Sort, ",", ")"} }
  private def parseSort(parsingLevel: ParsingLevel = both): Sort = {
    val name = parseId(parsingLevel)
    scanner.next() match {
      case '{' =>
        if (previousParsingLevel == meta) { // name is a meta-level id
          val metalevelSorts = Seq("#Char", "#CharList", "#String", "#Sort", "#SortList",
            "#Symbol", "#SymbolList", "#Variable", "#VariableList", "#Pattern", "#PatternList")
          if (metalevelSorts.contains(name)) {
            consumeWithLeadingWhitespaces("}") // no params
            b.CompoundSort(name, Seq.empty[Sort])
          }
          else {
            throw error("<Meta-Sort>", name) // not a valid meta-level sort
          }
        }
        else { // name is an object-level id
          val params = parseList(() => parseSort(objt), ',', '}') // params should be object-level
          consumeWithLeadingWhitespaces("}")
          b.CompoundSort(name, params)
        }
      case c =>
        scanner.putback(c)
        b.SortVariable(name)
    }
  }

  private def parseSortVariable(parsingLevel: ParsingLevel = both): SortVariable = {
    val name = parseId(parsingLevel)
    b.SortVariable(name)
  }

  private def parseSymbol(): Symbol = {
    val ctr = parseId()
    consumeWithLeadingWhitespaces("{")
    val params = parseList(() => parseSort(parsingLevel = previousParsingLevel), ',', '}')
    consumeWithLeadingWhitespaces("}")
    b.Symbol(ctr, params)
  }

  private def parseAlias(): Alias = {
    val ctr = parseId()
    consumeWithLeadingWhitespaces("{")
    val params = parseList(() => parseSort(parsingLevel = previousParsingLevel), ',', '}')
    consumeWithLeadingWhitespaces("}")
    b.Alias(ctr, params)
  }

  private def parseId(parsingLevel: ParsingLevel = both): String = {
    def loop(s: StringBuilder): String = {
      scanner.next() match {
        case c if isObjectIdChar(c) =>
          s += c; loop(s)
        case c => scanner.putback(c)
          s.toString()
      }
    }

    scanner.nextWithSkippingWhitespaces() match {
      case '#' => // going to parse a meta-level id: either #ID or #`ID
        previousParsingLevel = meta // if parse succeeds, the level is meta
        if (parsingLevel == both || parsingLevel == meta) {
          // expect both levels or only meta-level
          scanner.next() match {
            case '`' => // #`ID
              scanner.next() match {
                case c if isLetter(c) =>
                  "#`" + loop(new StringBuilder(c.toString()))
                case c => throw error("Meta-Identifier>", c)
              }
            case '\\' => // #\ID
              scanner.next() match {
                case c if isLetter(c) =>
                  "#\\" + loop(new StringBuilder(c.toString()))
                case c => throw error("Meta-Identifier>", c)
              }
            case c if isLetter(c) => // #ID
              "#" + loop(new StringBuilder(c.toString()))
            case err => throw error("<Meta-Identifier>", err)
          }
        }
        else {
          // expect only object-level
          throw error("<Object-Identifier>", '#')
        }
      case c if isLetter(c) => // going to parse an object-level id
        previousParsingLevel = objt // if parse succeeds, the level is object
        if (parsingLevel == both || parsingLevel == objt) {
          // expect both levels or only object-level
          val id = loop(new StringBuilder(c.toString))
          val kwds = Seq("module", "endmodule", "sort", "symbol", "alias", "axiom")
          if (kwds.contains(id)) {
            throw error("<Object-Identifier> should not be keywords", id)
          }
          id
        }
        else {
          // expect only meta-level
          throw error("<Meta-Identifier>", c)
        }
      case err => throw error("<Identifier>", err)
    }
  }

  private def isObjectIdChar(c: Char): Boolean = TextToKore.isObjectIdChar(c) // TODO(Daejun): more efficient way?

  private def isLetter(c: Char): Boolean = TextToKore.isLetter(c)

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
        "Expected " + expected + ", but " + actual
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
  def apply(b: Builders): TextToKore = new TextToKore(b)

  // Lexicon checkers

  def isLetter(c: Char): Boolean = {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
  }

  def isDigit(c: Char): Boolean = {
    '0' <= c && c <= '9'
  }

  def isObjectIdChar(c: Char): Boolean = {
    isLetter(c) || isDigit(c) || c == '\'' || c == '-'
  }

}
