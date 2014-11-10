package org.kframework.kore.outer

trait ModuleToString {
  self: Module =>
  override def toString = "module " + name + att.postfixString +
    "\n" + sentences.toList.sortBy(_.toString).reverse.map("  " + _).mkString("\n\n") + "\nendmodule"
}

trait DefinitionToString {
  self: Definition =>
  override def toString =
    requires.mkString("\n") +
      "\n\n" +
      modules.mkString("\n\n\n")
}

trait RuleToString {
  self: Rule =>
  override def toString = "  " + Seq("rule", body, "requires", requires, "ensures", ensures, att).mkString(" ")
}

trait SyntaxProductionToString {
  self: SyntaxProduction =>
  override def toString = "" + items.mkString(" ") + att
}

trait SyntaxSortToString {
  self: SyntaxSort =>
  override def toString() = "syntax " + sort + att.postfixString
}

// commented out until we figure out how to encode associativity
//trait BlockToString {
//  self: SyntaxProduction =>
//  override def toString = {
//    import Associativity._
//    val assocString = assoc match {
//      case Unspecified => ""
//      case Left => "left:\n"
//      case Right => "right:\n"
//      case NonAssoc => "non-assoc:\n"
//    }
//    assocString + productions.mkString("\n              |")
//  }
//}

trait TerminalToString {
  self: Terminal =>
  override def toString = "\"" + value + "\""
}
