package org.kframework


import java.util.{List, Map, Optional}

import org.kframework.definition.{Module, Rule}


trait RewriterConstructor extends (Module => Rewriter)

trait Rewriter {
  //  def normalize(k: K): K
  //  def substitute(k: K, s: KVariable => K): K

  //  def step(k: K): K

  /**
   * (disregard this javadoc comment for now)
   * Takes one rewriting step.
   * - for regular execution, it returns the next K or False (i.e. an empty Or)
   * - for symbolic execution, it can return any formula with symbolic constraints
   * - for search, it returns an Or with multiple ground terms as children
   */
  def execute(k: kore.K, depth: Optional[Integer]): kore.K


  def `match`(k: kore.K, rule: Rule): java.util.List[java.util.Map[kore.KVariable, kore.K]]


  /**
   * Execute a search of the Transition System.
   * @param initialConfig The State to begin searching from
   * @param depth No. of transitions to consider before termination (Depth of Tree to traverse). Empty represents unbounded
   * @param bound No. of states to consider as final results. Empty represents unbounded.
   * @param pattern The rule (pattern + side condition) that we're trying to find a substitution for.
   * @return A list of substitutions, denoting all the configurations matching the given rule.
   */
  
  def search(initialConfig: kore.K, depth: Optional[Integer], bound: Optional[Integer], pattern: Rule): List[_ <: Map[_ <: kore.KVariable, _ <: kore.K]]
}