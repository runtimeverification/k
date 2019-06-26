// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework.definition

import javax.annotation.Nonnull

import org.kframework.kore._
import org.kframework.attributes._
import org.kframework.kore.{KORE => con}
import org.kframework.utils.errorsystem.KEMException

import scala.annotation.meta.param
import scala.collection.Set

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

case class FlatModule(name: String, imports: Set[String], localSentences: Set[Sentence], @(Nonnull@param) val att: Att = Att.empty)
  extends OuterKORE with Sorting with Serializable {

  def toModule(allModules: Set[FlatModule], koreModules: scala.collection.mutable.Map[String, Module], visitedModules: Seq[FlatModule]): Module = {
    var mainModName = this.name
    var items = this.localSentences
    var importedModuleNames = this.imports
    var importedSyntax = importedModuleNames.map(m => Import.asSyntax(m))

    if (visitedModules.contains(this))
      throw KEMException.compilerError("Found circularity in module imports")
    // TODO: Implement CheckListDecl.check

    def resolveImport(importName: String): Module = {
      var baseName = Import.noSyntax(importName)
      var modOption = allModules.find(m => m.name.equals(baseName))
      if (modOption.nonEmpty) {
        var mod = modOption.get
        var result = koreModules.get(mod.name)
        if (result.isEmpty) {
          result = Some(mod.toModule(allModules, koreModules, this +: visitedModules))
        }
        if (Import.isSyntax(importName)) {
          result = Some(koreModules.get(importName).get)
        }
          result.get
      } else if (koreModules.contains(importName))
          koreModules.get(importName).get
        else
          throw KEMException.compilerError("Could not find module: " + importName)
    }

    var importedSyntaxModules = importedSyntax.map(resolveImport)
    var syntaxItems = items.filter(s => s.isSyntax)
    var att = this.att
    var newSyntaxModule = new Module(Import.asSyntax(this.name), importedSyntaxModules, syntaxItems, att)

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
