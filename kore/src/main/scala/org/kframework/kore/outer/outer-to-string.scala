package org.kframework.kore.outer

trait ModuleToString {
  self: Module =>
  override def toString = "module " + name + "\n" + sentences.toList.sortBy(_.toString).reverse.mkString("\n\n") + "\n\nendmodule"
}

trait DefinitionToString {
  self: Definition =>
  override def toString = modules.mkString("\n\n\n")
}

trait RuleToString {
  self: Rule =>
  override def toString = "  rule " + body + attributes
}

trait ConfigurationToString {
  self: Configuration =>
  override def toString = "  configuration " + contents
}

trait SyntaxProductionToString {
  self: SyntaxProduction =>
  override def toString = "" + items.mkString(" ") + attributes
}

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