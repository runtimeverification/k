// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework.definition

import javax.annotation.Nonnull

import org.kframework.kore._
import org.kframework.attributes._
import org.kframework.kore.{KORE => con}
import org.kframework.utils.errorsystem.KEMException

import scala.annotation.meta.param
import scala.collection.Set

import java.util.Optional

case class Configuration(body: K, ensures: K, att: Att = Att.empty) extends Sentence with OuterKORE {
  override val isSyntax = true
  override val isNonSyntax = true
  override def withAtt(att: Att) = Configuration(body, ensures, att)

  //  override def toString = "configuration " + xmlify(body) + " ensures " + ensures

  //  def xmlify(x: K): String = x match {
  //    case KApply(label, klist, att) if att.contains("cell") => {
  //      val atts = att.att.filterNot(_ == Configuration.cellMarker)
  //
  //      val attsString = if (atts.size > 0)
  //        " " + atts.map(xmlifyAttributes).mkString(" ")
  //      else
  //        ""
  //
  //      "<" + label.name + attsString + ">" +
  //        klist.map(xmlify _).mkString(" ") +
  //        "</" + label.name + ">"
  //    }
  //    //    case KBag(klist) =>
  //    //      if (klist.isEmpty)
  //    //        ".Bag"
  //    //      else
  //    //        klist map { xmlify _ } mkString " "
  //    case e => e.toString
  //  }
  //
  //  def xmlifyAttributes(x: K): String = x match {
  //    case KApply(label, klist, att) => label.name +
  //      (if (!klist.isEmpty)
  //        "=" + klist.map({ e: K => "\"" + e + "\"" }).mkString(" ")
  //      else
  //        "")
  //  }
}

case class Bubble(sentenceType: String, contents: String, att: Att = Att.empty) extends Sentence {
  override val isSyntax = sentenceType == "config" || sentenceType == "alias"
  override val isNonSyntax = sentenceType != "alias"
  override def withAtt(att: Att) = Bubble(sentenceType, contents, att)
}

object FlatModule {
  def apply(name: String, unresolvedLocalSentences: Set[Sentence]): FlatModule = {
    new FlatModule(name, Set(), unresolvedLocalSentences, Att.empty)
  }
}

case class Import(name: String, att: Att = Att.empty) extends HasLocation {
  override def location(): Optional[Location] = att.getOptional(classOf[Location])
  override def source(): Optional[Source] = att.getOptional(classOf[Source])
}

object Import {
  val syntaxString = "$SYNTAX"

  def isSyntax(name: String): Boolean = name.endsWith(syntaxString)

  def asSyntax(_import: Import): Import =
    if (isSyntax(_import.name))
      _import
    else
      Import(_import.name ++ syntaxString, _import.att)

  def noSyntax(name: String): String =
    if (isSyntax(name))
      name.dropRight(syntaxString.length)
    else
      name
}



case class FlatModule(name: String, imports: Set[Import], localSentences: Set[Sentence], @(Nonnull@param) val att: Att = Att.empty)
  extends OuterKORE with Sorting with Serializable {

  def toModule(allModules: Set[FlatModule], koreModules: scala.collection.mutable.Map[String, Module], visitedModules: Seq[FlatModule]): Module = {
    var mainModName = this.name
    var items = this.localSentences
    var importedModuleNames = this.imports
    var importedSyntax = importedModuleNames.map(m => Import.asSyntax(m))

    if (visitedModules.contains(this)) {
      var msg = "Found circularity in module imports: "
      visitedModules.foreach(m => msg += m.name + " < ")
      msg += visitedModules.head.name
      throw KEMException.compilerError(msg)
    }

    if (koreModules.contains(mainModName))
      return koreModules(mainModName)

    def resolveImport(_import: Import): Module = {
      var baseName = Import.noSyntax(_import.name)
      var modOption = allModules.find(m => m.name.equals(baseName))
      if (modOption.nonEmpty) {
        var mod = modOption.get
        var result = koreModules.get(mod.name)
        if (result.isEmpty) {
          result = Some(mod.toModule(allModules, koreModules, this +: visitedModules))
        }
        if (Import.isSyntax(_import.name)) {
          result = Some(koreModules.get(_import.name).get)
        }
          result.get
      } else if (koreModules.contains(_import.name))
          koreModules.get(_import.name).get
        else
          throw KEMException.compilerError("Could not find module: " + _import.name, _import)
    }

    var importedSyntaxModules = importedSyntax.map(resolveImport)
    var syntaxItems = items.filter(s => s.isSyntax)
    var att = this.att
    var newSyntaxModule = new Module(this.name + Import.syntaxString, importedSyntaxModules, syntaxItems, att)

    var importedModules = importedModuleNames.map(resolveImport) ++ Set(newSyntaxModule)

    var nonSyntaxItems = items.filter(s => s.isNonSyntax)
    var newModule = new Module(this.name, importedModules, nonSyntaxItems, att)

    newSyntaxModule.checkSorts()
    newModule.checkSorts()

    koreModules += ((newModule.name, newModule))
    koreModules += ((newSyntaxModule.name, newSyntaxModule))

    newModule
  }
}
