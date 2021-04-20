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
import scala.collection.concurrent.TrieMap

case class Configuration(body: K, ensures: K, att: Att = Att.empty) extends Sentence with OuterKORE {
  override val isSyntax = true
  override val isNonSyntax = true
  override def withAtt(att: Att) = Configuration(body, ensures, att)
}

case class Bubble(sentenceType: String, contents: String, att: Att = Att.empty) extends Sentence {
  override val isSyntax = sentenceType == "config" || sentenceType == "alias"
  override val isNonSyntax = sentenceType != "alias"
  override def withAtt(att: Att) = Bubble(sentenceType, contents, att)
}

case class Import(name: String, att: Att = Att.empty) extends HasLocation {
  override def location(): Optional[Location] = att.getOptional(classOf[Location])
  override def source(): Optional[Source] = att.getOptional(classOf[Source])
}

case class FlatModule(name: String, imports: Set[Import], localSentences: Set[Sentence], @(Nonnull@param) val att: Att = Att.empty)
  extends OuterKORE with Sorting with Serializable {
}

object FlatModule {
  def apply(name: String, unresolvedLocalSentences: Set[Sentence]): FlatModule = {
    new FlatModule(name, Set(), unresolvedLocalSentences, Att.empty)
  }

  def toModule(allModules:Set[FlatModule], previousModules:Set[Module]):Set[Module] = {
    val memoization:TrieMap[String, Module] = collection.concurrent.TrieMap[String, Module]()
    previousModules.map(m => memoization.put(m.name, m))
    allModules.map(m => toModuleRec(m, Seq()))
    def toModuleRec(m:FlatModule, visitedModules: Seq[FlatModule]):Module = {
      if (visitedModules.contains(m)) {
        var msg = "Found circularity in module imports: "
        visitedModules.foreach(m => msg += m.name + " < ")
        msg += visitedModules.head.name
        throw KEMException.compilerError(msg)
      }
      memoization.getOrElseUpdate(m.name, {
        new Module(
          m.name,
          m.imports.map(i => memoization.getOrElse(i.name,
            toModuleRec(allModules.find(f => f.name.equals(i.name)).getOrElse(throw KEMException.compilerError("Could not find module: " + i.name, i)), visitedModules :+ m))),
          m.localSentences,
          m.att
        )
      })
    }
    memoization.values.toSet
  }
}
