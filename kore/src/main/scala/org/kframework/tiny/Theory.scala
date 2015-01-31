package org.kframework.tiny

import org.kframework.koreimplementation.K


trait Theory {
  /**
   * Tells whether the proposition is valid in this theory.
   * If we cannot find an answer (e.g., we have symbolic values), return None
   * So None means the Proposition is satisfiable.
   */
  def apply(proposition: Proposition): Option[Boolean] = normalize(proposition) match {
    case True => Some(true)
    case False => Some(false)
    case _ => None
  }

  def normalize(k: Proposition): K
}
