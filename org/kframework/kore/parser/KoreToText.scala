package org.kframework.kore.parser

import org.apache.commons.lang3.StringEscapeUtils
import org.kframework.kore._
import org.kframework.kore

/** Function (i.e., unparser) from Kore to String. */
object KoreToText {
  // TODO(Daejun): more efficient implementation using StringBuilder instead of string concatenation

  /** Returns a string from [[kore.Definition]]. */
  def apply(d: Definition): String = {
    apply(d.att) + System.lineSeparator() + System.lineSeparator() +
      d.modules.map(apply).mkString(System.lineSeparator() + System.lineSeparator()) + System.lineSeparator()
  }

  /** Returns a string from [[kore.Module]]. */
  def apply(m: Module): String = {
    "module " + apply(m.name.str) + System.lineSeparator() +
      m.sentences.map(s => "  " + apply(s)).mkString(System.lineSeparator()) + System.lineSeparator() +
      "endmodule " + apply(m.att)
  }

  /** Returns a string from [[kore.Sentence]]. */
  def apply(s: Sentence): String = s match {
    case Import(ModuleName(name), att) =>
      "import " + apply(name) + " " + apply(att)
    case SortDeclaration(sort, att) =>
      "sort" + apply(sort) + " " + apply(att)
    // case SymbolDeclaration(sort, Symbol(label), args, att) =>
    //   "syntax " + apply(sort) + " ::= " + apply(label) + "(" + args.map(x => apply(x.str)).mkString(",") + ") " + apply(att)
    case Rule(pattern, att) =>
      "rule " + apply(pattern) + " " + apply(att)
    case Axiom(params, pattern, att) =>
      "axiom " + "{" + params.map(s => apply(s)).mkString(",") + "}" + apply(pattern) + " " + apply(att)
  }

  /** Returns a string from [[kore.Sort]]. */
  def apply(sort: Sort): String = {
    sort match {
      case SortVariable(name) => apply(name)
      case CompoundSort(ctr, params) => apply(ctr) + "{" + params.map(s => apply(s)).mkString(",") + "}"
    }
  }

  /** Returns a string from [[kore.Pattern]]. */
  def apply(pat: Pattern): String = pat match {
    case SortedVariable(Name(name), sort) => apply(name) + ":" + apply(sort)
    case Application(Symbol(label), args) => apply(label) + "(" + args.map(apply).mkString(",") + ")"
    case DomainValue(Symbol(label), value) => apply(label) + "(\"" + StringEscapeUtils.escapeJava(value.str) + "\")"
    case Top(s) => "\\top" + "{" + apply(s) + "}" + "()"
    case Bottom() => "\\bottom()"
    case And(p, q) => "\\and(" + apply(p) + "," + apply(q) + ")"
    case Or(p, q) => "\\or(" + apply(p) + "," + apply(q) + ")"
    case Not(p) => "\\not(" + apply(p) + ")"
    case Implies(p, q) => "\\implies(" + apply(p) + "," + apply(q) + ")"
    case Exists(v, p) => "\\exists(" + apply(v) + "," + apply(p) + ")"
    case ForAll(v, p) => "\\forall(" + apply(v) + "," + apply(p) + ")"
    case Next(p) => "\\next(" + apply(p) + ")"
    case Rewrite(p, q) => "\\rewrite(" + apply(p) + "," + apply(q) + ")"
    case Equals(p, q) => "\\equals(" + apply(p) + "," + apply(q) + ")"
  }

  /** Returns a string from [[kore.Attributes]]. */
  def apply(att: Attributes): String = {
    "[" + att.patterns.map(apply).mkString(",") + "]"
  }


  /** Normalizes the string of Sort, Name, or Symbol.
    *
    * @param s the string value of Sort, Name, or Symbol.
    * @return the string enclosed in back-quotes if it contains non-symbol characters,
    *         otherwise, the input string as it is.
    */
  def apply(s: String): String = {
    if (s == "" || s.exists(c => !TextToKore.isSymbolChar(c))) {
      "`" + s + "`"
    } else s
  }

}
