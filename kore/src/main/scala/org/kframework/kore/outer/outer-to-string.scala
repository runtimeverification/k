package org.kframework.kore.outer

import org.apache.commons.lang3.StringEscapeUtils

trait ModuleToString {
  self: Module =>
  override def toString = "module " + name + att.postfixString +
    "\n" + sentences.toList.map(_.toString).sorted.reverse.map("  " + _).mkString("\n") + "\nendmodule"
}

trait DefinitionToString {
  self: Definition =>
  override def toString =
    requires.mkString("\n") +
      "\n\n" +
      modules.toList.map(_.toString).sorted.mkString("\n\n\n")
}

trait RuleToString {
  self: Rule =>
  override def toString = Seq("rule", body, "requires", requires, "ensures", ensures, att).mkString(" ")
}

trait SyntaxProductionToString {
  self: SyntaxProduction =>
  override def toString = "syntax " + sort + " ::= " + items.mkString(" ") + att.postfixString
}

trait SyntaxSortToString {
  self: SyntaxSort =>
  override def toString() = "syntax " + sort + att.postfixString
}

trait ImportToString {
  self: Import =>
  override def toString() = "imports " + what + att.postfixString
}

trait TerminalToString {
  self: Terminal =>
  override def toString = "\"" + value + "\""
}

trait NonTerminalToString {
  self: NonTerminal =>
  override def toString = sort.toString()
}

trait RegexTerminalToString {
  self: RegexTerminal =>
  override def toString = {
    "r\"" + StringEscapeUtils.escapeJava(regex) + "\""
  }
}

trait SyntaxAssociativityToString {
  self: SyntaxAssociativity =>
  override def toString = {
    val assocString = assoc match {
      case Associativity.Left => "left"
      case Associativity.Right => "right"
      case Associativity.NonAssoc => "non-assoc"
    }
    "syntax associativity " + assocString + " " + tags.mkString(" ") + att.postfixString
  }
}

trait ContextToString {
  self: Context =>
  override def toString = "context " + body + " requires " + requires
}

trait SyntaxPriorityToString {
  self: SyntaxPriority =>
  override def toString = "syntax priority " + priorities.map { _.mkString(" ") }.mkString(" > ")
}

trait TagToString {
  self: Tag =>
  override def toString = name
}
