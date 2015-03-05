package org.kframework

import org.kframework.definition.Module
import org.kframework.kore.{K, KVariable}

trait RewriterConstructor extends (Module => Rewriter)

trait Rewriter {
  def normalize(k: K): K
  def substitute(k: K, s: KVariable => K): K

  /**
   * Takes one rewriting step.
   *  - for regular execution, it returns the next K or False (i.e. an empty Or)
   *  - for symbolic execution, it can return any formula with symbolic constraints
   *  - for search, it returns an Or with multiple ground terms as children
   */
  def step(k: K): K

  def rewrite(k: K): K
}