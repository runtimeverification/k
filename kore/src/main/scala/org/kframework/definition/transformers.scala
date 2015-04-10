// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.definition

import org.kframework.definition

case class ModuleTransformer(f: Module => Module) extends (Module => Module) {
  val memoization = collection.mutable.HashMap[Module, Module]()

  override def apply(input: Module): Module = {
    memoization.getOrElseUpdate(input, f(Module(input.name, input.imports map this, input.localSentences, input.att)))
  }
}

object DefinitionTransformer {
  def from(f: java.util.function.UnaryOperator[Module]): DefinitionTransformer = DefinitionTransformer(f(_))
}

case class DefinitionTransformer(f: Module => Module) extends (Definition => Definition) {
  val moduleTransformer = ModuleTransformer(f)

  override def apply(d: Definition): Definition = {
    definition.Definition(
      moduleTransformer(d.mainModule),
      moduleTransformer(d.mainSyntaxModule),
      d.modules map moduleTransformer)
  }
}
