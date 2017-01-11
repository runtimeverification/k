package org.kframework.minikore

import org.apache.commons.lang3.StringEscapeUtils
import org.kframework.minikore.MiniKore._

object MiniToText {
  // TODO(Daejun): more efficient implementation using StringBuilder instead of string concatenation

  def apply(d: Definition): String = {
    apply(d.att) + "\n\n" +
    d.modules.map(apply).mkString("\n\n")
  }

  def apply(m: Module): String = {
    "module " + m.name + "\n" +
      m.sentences.map(s => "  " + apply(s)).mkString("\n") + "\n" +
    "endmodule " + apply(m.att)
  }

  def apply(s: Sentence): String = s match {
    case Import(name, att) =>
      "imports " + name + " " + apply(att)
    case SortDeclaration(sort, att) =>
      "syntax " + apply(sort) + " " + apply(att)
    case SymbolDeclaration(sort, label, args, att) =>
      "syntax " + apply(sort) + " ::= " + apply(label) + "(" + args.map(apply).mkString(",") + ") " + apply(att)
    case Rule(pattern, att) =>
      "rule " + apply(pattern) + " " + apply(att)
    case Axiom(pattern, att) =>
      "axiom " + apply(pattern) + " " + apply(att)
  }

  def apply(pat: Pattern): String = pat match {
    case Variable(name, sort) => apply(name) + ":" + apply(sort)
    case Application(label, args) => apply(label) + "(" + args.map(apply).mkString(",") + ")"
    case DomainValue(label, value) => apply(label) + "(\"" + StringEscapeUtils.escapeJava(value) + "\")"
    case True() => "\\true()"
    case False() => "\\false()"
    case And(p, q) => "\\and(" + apply(p) + "," + apply(q) + ")"
    case Or(p, q) => "\\or(" + apply(p) + "," + apply(q) + ")"
    case Not(p) => "\\not(" + apply(p) + ")"
    case Implies(p, q) => "\\implies(" + apply(p) + "," + apply(q) + ")"
    case Exists(v, p) => "\\exists(" + apply(v) + "," + apply(p) + ")"
    case ForAll(v, p) => "\\forall(" + apply(v) + "," + apply(p) + ")"
    case Next(p) => "\\next(" + apply(p) + ")"
    case Rewrite(p, q) => "\\rewrite(" + apply(p) + "," + apply(q) + ")"
    case Equal(p, q) => "\\equal(" + apply(p) + "," + apply(q) + ")"
  }

  def apply(att: Attributes): String = {
    "[" + att.map(apply).mkString(",") + "]"
  }

  def apply(s: String): String = {
    if (s == "" || s.exists(c => !TextToMini.isSymbolChar(c))) {
      "`" + s + "`"
    } else s
  }

}
