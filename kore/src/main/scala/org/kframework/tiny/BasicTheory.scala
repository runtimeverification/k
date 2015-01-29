package org.kframework.tiny

import org.kframework.kore.{UglyHack, K}

import UglyHack._

/**
 * Created by cos on 1/28/15.
 */
class BasicTheory(reducer: K => Option[K]) extends Theory {
  /**
   * Tells whether the proposition is valid in this theory.
   * If we cannot find an answer (e.g., we have symbolic values), return None
   * So None means the Proposition is satisfiable.
   */
  def normalize(k: K): K = {
    k.transform(reducer)
  }
}
