package org.kframework.kore.parser

import org.kframework.kore._
import org.kframework.kore

/** Function (i.e., unparser) from Kore to String. */

object KoreToText {
  // TODO(Daejun): more efficient implementation using StringBuilder instead of string concatenation

  /** Returns a string from [[kore.Definition]]. */
  def apply(d: Definition): String = {
    apply(d.att) +
    System.lineSeparator() +
    System.lineSeparator() +
    d.modules.map(apply).mkString(System.lineSeparator() + System.lineSeparator()) +
    System.lineSeparator()
  }

  /** Returns a string from [[kore.Module]]. */
  def apply(m: Module): String = {
    "module " +
    apply(m.name.str) +
    System.lineSeparator() +
    m.sentences.map(s => "  " + apply(s)).mkString(System.lineSeparator()) +
    System.lineSeparator() +
    "endmodule " +
    apply(m.att)
  }

  /** Returns a string from [[kore.Sentence]]. */
  def apply(d: Sentence): String = d match {

    case Import(ModuleName(name), att) =>
      "import " + apply(name) + " " + apply(att)

    case SortDeclaration(params, sort, att) =>
      "sort{" +
      params.map(s => apply(s)).mkString(",") +
      "} " +
      apply(sort) +
      " " +
      apply(att)

    case SymbolDeclaration(symbol, argSorts, returnSort, att) =>
      "symbol " +
      apply(symbol) +
      "(" +
      argSorts.map(s => apply(s)).mkString(",") +
      ") : " +
      apply(returnSort) +
      " " +
      apply(att)

    case AliasDeclaration(alias, argSorts, returnSort, att) =>
      "alias " +
      apply(alias) +
      "(" +
      argSorts.map(s => apply(s)).mkString(",") +
      ") : " +
      apply(returnSort) +
      " " +
      apply(att)

    case AxiomDeclaration(params, pattern, att) =>
      "axiom{" +
      params.map(s => apply(s)).mkString(",") +
      "} " +
      apply(pattern) +
      " " +
      apply(att)
  }

  /** Returns a string from [[kore.Sort]]. */
  def apply(s: Sort): String = s match {
      case SortVariable(name) =>
        apply(name)
      case CompoundSort(ctr, params) =>
        apply(ctr) + "{" + params.map(s => apply(s)).mkString(",") + "}"
  }

  /** Returns a string from [[kore.SymbolOrAlias]] */
  def apply(head: SymbolOrAlias): String = {
    apply(head.ctr) + "{" + head.params.map(s => apply(s)).mkString(",") + "}"
  }

  /** Returns a string from [[kore.Symbol]] */
  def apply(symbol: Symbol): String = {
    apply(symbol.ctr) + "{" + symbol.params.map(s => apply(s)).mkString(",") + "}"
  }

  /** Returns a string from [[kore.Alias]] */
  def apply(alias: Alias): String = {
    apply(alias.ctr) + "{" + alias.params.map(s => apply(s)).mkString(",") + "}"
  }

  /** Returns a string from [[kore.Pattern]]. */
  def apply(pat: Pattern): String = pat match {
    case Variable(name, sort) =>
      apply(name) + ":" + apply(sort)
    case Application(head, args) =>
      apply(head) + "(" + args.map(apply).mkString(",") + ")"
    case Top(s) =>
      "\\top" + "{" + apply(s) + "}" + "()"
    case Bottom(s) =>
      "\\bottom" + "{" + apply(s) + "}" + "()"
    case And(s, p, q) =>
      "\\and" + "{" + apply(s) + "}" +
        "(" + apply(p) + "," + apply(q) + ")"
    case Or(s, p, q) =>
      "\\or" + "{" + apply(s) + "}" +
        "(" + apply(p) + "," + apply(q) + ")"
    case Not(s, p) =>
      "\\not{" + apply(s) + "}" +
        "(" + apply(p) + ")"
    case Implies(s, p, q) =>
      "\\implies" + "{" + apply(s) + "}" +
        "(" + apply(p) + "," + apply(q) + ")"
    case Iff(s, p, q) =>
      "\\iff" + "{" + apply(s) + "}" +
        "(" + apply(p) + "," + apply(q) + ")"
    case Exists(s, v, p) =>
      "\\exists" + "{" + apply(s) + "}" +
        "(" + apply(v) + "," + apply(p) + ")"
    case Forall(s, v, p) =>
      "\\forall" + "{" + apply(s) + "}" +
        "(" + apply(v) + "," + apply(p) + ")"
    case Next(s, p) =>
      "\\next" + "{" + apply(s) + "}" +
        "(" + apply(p) + ")"
    case Rewrites(s, rs, p, q) =>
      "\\rewrites" + "{" + apply(s) + "," + apply(rs) + "}" +
        "(" + apply(p) + "," + apply(q) + ")"
    case Equals(s1, s2, p, q) =>
      "\\equals" + "{" + apply(s1) + "," + apply(s2) + "}" +
        "(" + apply(p) + "," + apply(q) + ")"
    case Mem(s, rs, x, p) =>
      "\\mem" + "{" + apply(s) + "," + apply(rs) + "}" +
        "(" + apply(x) + "," + apply(p) + ")"
    case Subset(s, rs, p, q) =>
      "\\subset" + "{" + apply(s) + "," + apply(rs) + "}" +
        "(" + apply(p) + "," + apply(q) + ")"
    case DomainValue(sortStr, valueStr) =>
      "\\domainvalue" + apply(sortStr) + "," + apply(valueStr) + ")"
    case StringLiteral(str) =>
      "\"" + str + "\""
  }

  /** Returns a string from [[kore.Attributes]]. */
  def apply(att: Attributes): String = {
    "[" + att.patterns.map(apply).mkString(",") + "]"
  }

  def apply(s: String): String = s

  /** Normalizes the string of Sort, Name, or Symbol.
    *
    * param s the string value of Sort, Name, or Symbol.
    * return the string enclosed in back-quotes if it contains non-symbol characters,
    *         otherwise, the input string as it is.
  def apply(s: String): String = {
    if (s == "" || s.exists(c => !TextToKore.isSymbolChar(c))) {
      "`" + s + "`"
    } else s
  }
  */

}
