package org.kframework.minikore.parser

import org.apache.commons.lang3.StringEscapeUtils
import org.kframework.minikore.implementation.MiniKore.{Definition, Import, Rule, Axiom, Module, Attributes, Sentence, SymbolDeclaration, SortDeclaration}
import org.kframework.minikore.interfaces.PatternInterface._

/** Function (i.e., unparser) from MiniKore to String. */
object MiniToText {
  // TODO(Daejun): more efficient implementation using StringBuilder instead of string concatenation

  /** Returns a string from [[org.kframework.minikore.implementation.MiniKore.Definition]]. */
  def apply(d: Definition): String = {
    apply(d.att) + System.lineSeparator() + System.lineSeparator() +
      d.modules.map(apply).mkString(System.lineSeparator() + System.lineSeparator()) + System.lineSeparator()
  }

  /** Returns a string from [[org.kframework.minikore.implementation.MiniKore.Module]]. */
  def apply(m: Module): String = {
    "module " + m.name + System.lineSeparator() +
      m.sentences.map(s => "  " + apply(s)).mkString(System.lineSeparator()) + System.lineSeparator() +
      "endmodule " + apply(m.att)
  }

  /** Returns a string from [[org.kframework.minikore.implementation.MiniKore.Sentence]]. */
  def apply(s: Sentence): String = s match {
    case Import(name, att) =>
      "import " + name + " " + apply(att)
    case SortDeclaration(sort, att) =>
      "syntax " + apply(sort) + " " + apply(att)
    case SymbolDeclaration(sort, label, args, att) =>
      "syntax " + apply(sort) + " ::= " + apply(label) + "(" + args.map(apply).mkString(",") + ") " + apply(att)
    case Rule(pattern, att) =>
      "rule " + apply(pattern) + " " + apply(att)
    case Axiom(pattern, att) =>
      "axiom " + apply(pattern) + " " + apply(att)
  }

  /** Returns a string from [[org.kframework.minikore.interfaces.PatternInterface.Pattern]]. */
  def apply(pat: Pattern): String = pat match {
    case Variable(name, sort) => apply(name) + ":" + apply(sort)
    case Application(label, args) => apply(label) + "(" + args.map(apply).mkString(",") + ")"
    case DomainValue(label, value) => apply(label) + "(\"" + StringEscapeUtils.escapeJava(value) + "\")"
    case Top() => "\\top()"
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

  /** Returns a string from [[org.kframework.minikore.implementation.MiniKore.Attributes]]. */
  def apply(att: Attributes): String = {
    "[" + att.map(apply).mkString(",") + "]"
  }

  /** Normalizes the string of Sort, Name, or Symbol.
    *
    * @param s the string value of Sort, Name, or Symbol.
    * @return the string enclosed in back-quotes if it contains non-symbol characters,
    *         otherwise, the input string as it is.
    */
  def apply(s: String): String = {
    if (s == "" || s.exists(c => !TextToMini.isSymbolChar(c))) {
      "`" + s + "`"
    } else s
  }

}
