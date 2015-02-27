package org.kframework.tiny


import org.kframework.definition

class Rewriter(module: definition.Module) {
  val cons = new Constructors(module)

  import cons._

  val rules = module.rules map { r => Rule(convert(r.body), convert(r.requires)) }

  def rewrite(k: K): Set[K] = {
    val newKs = rules flatMap { r => r(k) }

    newKs
  }
}
