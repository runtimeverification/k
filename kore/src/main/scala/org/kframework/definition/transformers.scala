// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.definition

import org.kframework.attributes.{Source, Location}
import org.kframework.definition
import org.kframework.kore.K
import org.kframework.utils.errorsystem.KEMException

object ModuleTransformer {
  def from(f: java.util.function.UnaryOperator[Module], name: String): ModuleTransformer = ModuleTransformer(f(_), name)

  def fromSentenceTransformer(f: java.util.function.UnaryOperator[Sentence], name: String): ModuleTransformer =
    fromSentenceTransformer((m: Module, s: Sentence) => f(s), name)

  def fromSentenceTransformer(f: (Module, Sentence) => Sentence, name: String): ModuleTransformer =
    ModuleTransformer(m => {
      val newSentences = m.localSentences map { s =>
        try {
          f(m, s)
        } catch {
          case e: KEMException =>
            e.exception.addTraceFrame("while executing phase \"" + name + "\" on sentence at " + s.att.get(classOf[Source]).map(_.toString).getOrElse("<none>") + ":" + s.att.get(classOf[Location]).map(_.toString).getOrElse("<none>"))
            throw e
        }
      }
      if (newSentences != m.localSentences)
        Module(m.name, m.imports, newSentences, m.att)
      else
        m
    }, name)

  def fromRuleBodyTranformer(f: java.util.function.UnaryOperator[K], name: String): ModuleTransformer =
    fromSentenceTransformer(_ match { case r: Rule => r.copy(body = f(r.body)); case s => s }, name)

  def fromRuleBodyTranformer(f: K => K, name: String): ModuleTransformer =
    fromSentenceTransformer(_ match { case r: Rule => r.copy(body = f(r.body)); case s => s }, name)

  def apply(f: Module => Module, name: String): ModuleTransformer = f match {
    case f: ModuleTransformer => f
    case _ => new ModuleTransformer(f, name)
  }
}

/**
 * Transform all modules, transforming each module after its imports.
 * The f function take a module with all the imported modules already transformed, and changes the current module.
 */
class ModuleTransformer(f: Module => Module, name: String) extends (Module => Module) {
  val memoization = collection.concurrent.TrieMap[Module, Module]()

  override def apply(input: Module): Module = {
    memoization.getOrElseUpdate(input, {
      var newImports = input.imports map this
      if (newImports != input.imports)
        f(Module(input.name, newImports, input.localSentences, input.att))
      else
        f(input)
    })
  }
}

object DefinitionTransformer {
  def fromSentenceTransformer(f: java.util.function.UnaryOperator[Sentence], name: String): DefinitionTransformer =
    DefinitionTransformer(ModuleTransformer.fromSentenceTransformer(f, name))

  def fromSentenceTransformer(f: (Module, Sentence) => Sentence, name: String): DefinitionTransformer =
    DefinitionTransformer(ModuleTransformer.fromSentenceTransformer(f, name))

  def fromRuleBodyTranformer(f: java.util.function.UnaryOperator[K], name: String): DefinitionTransformer =
    DefinitionTransformer(ModuleTransformer.fromRuleBodyTranformer(f, name))

  def fromRuleBodyTranformer(f: K => K, name: String): DefinitionTransformer =
    DefinitionTransformer(ModuleTransformer.fromRuleBodyTranformer(f, name))

  def from(f: java.util.function.UnaryOperator[Module], name: String): DefinitionTransformer = DefinitionTransformer(f(_), name)

  def apply(f: Module => Module): DefinitionTransformer = new DefinitionTransformer(f)

  def apply(f: Module => Module, name: String): DefinitionTransformer = new DefinitionTransformer(ModuleTransformer(f, name))
}

class DefinitionTransformer(moduleTransformer: Module => Module) extends (Definition => Definition) {
  override def apply(d: Definition): Definition = {
    definition.Definition(
      moduleTransformer(d.mainModule),
      moduleTransformer(d.mainSyntaxModule),
      d.entryModules map moduleTransformer)
  }
}
