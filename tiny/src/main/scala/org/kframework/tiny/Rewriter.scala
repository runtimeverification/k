package org.kframework.tiny


import org.kframework.definition

class Rewriter(module: definition.Module) extends org.kframework.Rewriter {
  val cons = new Constructors(module)

  import cons._

  val rules = module.rules map { r => Rule(convert(r.body), convert(r.requires)) }

  def rewrite(k: K): Set[K] = rules flatMap { r => r(k) }

  def rewriteRepeat(k: K): Set[K] = {
    val newKs = rewrite(k)
    println(newKs)
    if (newKs.size == 0)
      Set(k)
    else {
      newKs flatMap { rewriteRepeat(_) }
    }
  }

  def rewriteToFixpoint(k: K)(implicit sofar: Set[K] = Set()): Set[K] = {
    val newKs = rewrite(k) &~ sofar
    if (newKs.size == 0)
      sofar
    else {
      sofar | (newKs flatMap { rewriteToFixpoint(_)(sofar | newKs) })
    }
  }
}
