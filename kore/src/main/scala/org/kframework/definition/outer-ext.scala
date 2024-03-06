// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework.definition

import java.util.Optional
import javax.annotation.Nonnull
import org.kframework.attributes._
import org.kframework.kore._
import org.kframework.utils.errorsystem.KEMException
import scala.annotation.meta.param
import scala.collection.immutable
import scala.collection.mutable
import scala.collection.Set

case class Configuration(body: K, ensures: K, att: Att = Att.empty)
    extends Sentence
    with OuterKORE {
  override val isSyntax          = true
  override val isNonSyntax       = true
  override def withAtt(att: Att) = Configuration(body, ensures, att)
}

case class Bubble(sentenceType: String, contents: String, att: Att = Att.empty) extends Sentence {
  override val isSyntax          = sentenceType == "config" || sentenceType == "alias"
  override val isNonSyntax       = sentenceType != "alias"
  override def withAtt(att: Att) = Bubble(sentenceType, contents, att)
}

case class FlatImport(name: String, isPublic: Boolean, att: Att = Att.empty) extends HasLocation {
  override def location(): Optional[Location] = att.getOptional(Att.LOCATION, classOf[Location])
  override def source(): Optional[Source]     = att.getOptional(Att.SOURCE, classOf[Source])
}

case class FlatModule(
    name: String,
    imports: Set[FlatImport],
    localSentences: Set[Sentence],
    @(Nonnull @param) val att: Att = Att.empty
) extends OuterKORE
    with Sorting
    with Serializable {}

object FlatModule {
  def apply(name: String, unresolvedLocalSentences: Set[Sentence]): FlatModule =
    new FlatModule(name, Set(), unresolvedLocalSentences, Att.empty)

  /**
   * Gets a list of {@link FlatModule} and returns a set of {@link Module} .
   * @param allModules
   *   List of FlatModules to be transformed. The order matters when reporting circular imports.
   * @param previousModules
   *   A set of Modules already built. New modules will be added to this set.
   * @return
   *   The set of Modules, directly connected and maximally shared.
   */
  def toModules(
      allModules: immutable.Seq[FlatModule],
      previousModules: Set[Module]
  ): Set[Module] = {
    val memoization: mutable.HashMap[String, Module] = collection.mutable.HashMap[String, Module]()
    previousModules.map(m => memoization.put(m.name, m))
    def toModuleRec(m: FlatModule, visitedModules: immutable.Seq[FlatModule]): Module = {
      if (visitedModules.contains(m)) {
        var msg = "Found circularity in module imports: "
        visitedModules.reverse.foreach(m => msg += m.name + " < ")
        msg += visitedModules.last.name
        throw KEMException.compilerError(msg)
      }
      memoization.getOrElseUpdate(
        m.name, {
          // transform all imports into Module
          val f = (i: FlatImport) =>
            Import(
              memoization.getOrElse(
                i.name
                // if can't find the Module in memoization, build a new one
                ,
                toModuleRec(
                  allModules
                    .find(f => f.name.equals(i.name))
                    .getOrElse(
                      throw KEMException.compilerError("Could not find module: " + i.name, i)
                    ),
                  visitedModules :+ m
                )
              ),
              i.isPublic
            )
          val newImports = m.imports.map(f)
          val newM       = new Module(m.name, newImports, m.localSentences, m.att)
          newM.checkSorts()
          newM.checkUserLists()
          newM
        }
      )
    }
    allModules.map(m => toModuleRec(m, immutable.Seq()))
    memoization.values.toSet
  }
}
