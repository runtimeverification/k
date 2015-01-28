package org.kframework.tiny

import org.kframework.kore.K

class BasicTheory(r: Strategy.Rule) extends Theory {
  /**
   * Tells whether the proposition is valid in this theory.
   * If we cannot find an answer (e.g., we have symbolic values), return None
   * So None means the Proposition is satisfiable.
   */
  override def apply(proposition: Proposition): Option[Boolean] = {
    def applyR(x: K): Option[K] = r(x).headOption

//    proposition.transform((apply _).)
    ???
  }
}
