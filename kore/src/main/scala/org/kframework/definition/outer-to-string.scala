package org.kframework.definition

import org.apache.commons.lang3.StringEscapeUtils
import collection._

trait ModuleToString {
  self: Module =>
  override def toString = "module " + name + att.postfixString + "\n" +
    prettyPrintSet(imports map {"imports " + _.name}) +
    prettyPrintSet(localSentences) +
    "endmodule"

  def prettyPrintSet(s: Set[_]) = {
    s.toList.map(_.toString).sorted.reverse.map("  " + _).mkString("\n") +
      (if (s.size > 0) "\n" else "")
  }
}

trait DefinitionToString {
  self: Definition =>
  override def toString = modules.toList.map(_.toString).sorted.mkString("\n\n\n")
}

trait RuleToString {
  self: Rule =>
  override def toString = Seq("rule", body, "requires", requires, "ensures", ensures, att).mkString(" ")
}

trait ProductionToString {
  self: Production =>
  override def toString = "syntax " + sort + " ::= " + items.mkString(" ") + att.postfixString
}

trait SyntaxSortToString {
  self: SyntaxSort =>
  override def toString() = "syntax " + sort + att.postfixString
}

trait TerminalToString {
  self: Terminal =>
  override def toString = "\"" + StringEscapeUtils.escapeJava(value) + "\""
}

trait NonTerminalToString {
  self: NonTerminal =>
  override def toString = sort.toString()
}

trait RegexTerminalToString {
  self: RegexTerminal =>
  override def toString = {
    "r\"" + StringEscapeUtils.escapeJava(
      (if ("#" == precedeRegex) "" else "(?<!" + precedeRegex + ")" ) +
      regex +
      (if ("#" == followRegex) "" else "(?!" + precedeRegex + ")" )
    ) + "\""
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
  override def toString = "syntax priority " + priorities.map {_.mkString(" ")}.mkString(" > ")
}

trait TagToString {
  self: Tag =>
  override def toString = name
}
