// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.definition

import org.kframework.attributes.Att
import org.kframework.attributes.Location
import org.kframework.attributes.Source
import org.kframework.utils.StringUtil
import scala.collection.{ IndexedSeq => _, Seq => _, _ }

trait ModuleToString {
  self: Module =>
  override def toString = "module " + name + att.postfixString + "\n" +
    prettyPrintSet(fullImports.map("imports " + _.name)) +
    prettyPrintSet(localSentences) +
    "endmodule"

  def prettyPrintSet(s: Set[_]) =
    s.toList.map(_.toString).sorted.reverse.map("  " + _).mkString("\n") +
      (if (s.size > 0) "\n" else "")
}

trait DefinitionToString {
  self: Definition =>
  override def toString = modules.toList.map(_.toString).sorted.mkString("\n\n\n")
}

trait RuleToString {
  self: Rule =>
  override def toString =
    Seq("rule", body, "requires", requires, "ensures", ensures, att).mkString(" ")
}

trait ClaimToString {
  self: Claim =>
  override def toString =
    Seq("claim", body, "requires", requires, "ensures", ensures, att).mkString(" ")
}

trait ProductionToString {
  self: Production =>
  override def toString = "syntax " + (if (params.nonEmpty) { "{" + params.mkString(", ") + "} " }
                                       else "") + sort + " ::= " + items
    .mkString(" ") + att
    .remove(Att.SOURCE, classOf[Source])
    .remove(Att.LOCATION, classOf[Location])
    .postfixString
}

trait SyntaxSortToString {
  self: SyntaxSort =>
  override def toString() = "syntax " + sort + att.postfixString
}

trait SortSynonymToString {
  self: SortSynonym =>
  override def toString() = "syntax " + newSort + " = " + oldSort + att.postfixString
}

trait SyntaxLexicalToString {
  self: SyntaxLexical =>
  override def toString() =
    "syntax lexical " + name + " = r" + StringUtil.enquoteKString(regex) + att.postfixString
}

trait TerminalToString {
  self: Terminal =>
  override def toString = StringUtil.enquoteKString(value)
}

trait NonTerminalToString {
  self: NonTerminal =>
  override def toString = if (name.isDefined) name.get + ":" + sort.toString() else sort.toString()
}

trait RegexTerminalToString {
  self: RegexTerminal =>
  override def toString =
    "r" + StringUtil.enquoteKString(
      (if ("#" == precedeRegex) "" else "(?<!" + precedeRegex + ")") +
        regex +
        (if ("#" == followRegex) "" else "(?!" + followRegex + ")")
    )
}

trait SyntaxAssociativityToString {
  self: SyntaxAssociativity =>
  override def toString = {
    val assocString = assoc match {
      case Associativity.Left        => "left"
      case Associativity.Right       => "right"
      case Associativity.NonAssoc    => "non-assoc"
      case Associativity.Unspecified => "unspecified"
    }
    "syntax associativity " + assocString + " " + tags.mkString(" ") + att.postfixString
  }
}

trait ContextToString {
  self: Context =>
  override def toString = Seq("context", body, "requires", requires, att).mkString(" ")
}

trait ContextAliasToString {
  self: ContextAlias =>
  override def toString = Seq("context", "alias", body, "requires", requires, att).mkString(" ")
}

trait SyntaxPriorityToString {
  self: SyntaxPriority =>
  override def toString = "syntax priority " + priorities.map(_.mkString(" ")).mkString(" > ")
}

trait TagToString {
  self: Tag =>
  override def toString = name
}
