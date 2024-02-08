// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.rewriter

import java.util.Optional
import org.kframework.definition.Module
import org.kframework.definition.Rule
import org.kframework.kore
import org.kframework.RewriterResult

trait Rewriter {
  //  def normalize(k: K): K
  //  def substitute(k: K, s: KVariable => K): K

  //  def step(k: K): K

  /**
   * (disregard this javadoc comment for now)
   *
   * Takes one rewriting step.
   *   - for regular execution, it returns the next K or False (i.e. an empty Or)
   *   - for symbolic execution, it can return any formula with symbolic constraints
   *   - for search, it returns an Or with multiple ground terms as children
   */
  def execute(k: kore.K, depth: Optional[Integer]): RewriterResult

  def `match`(k: kore.K, rule: Rule): kore.K

  /**
   * Execute a search of the Transition System.
   * @param initialConfiguration
   *   The configuration to begin searching from.
   * @param depth
   *   No. of transitions to consider before termination (Depth of Tree to traverse). Empty
   *   represents unbounded.
   * @param bound
   *   No. of states to consider as final results. Empty represents unbounded.
   * @param pattern
   *   The rule (pattern + side condition) that we're trying to find a substitution for.
   * @return
   *   A list of substitutions, denoting all the configurations matching the given rule.
   */
  def search(
      initialConfiguration: kore.K,
      depth: Optional[Integer],
      bound: Optional[Integer],
      pattern: Rule
  ): kore.K

  def prove(rules: Module, reuseDef: java.lang.Boolean): RewriterResult

}
