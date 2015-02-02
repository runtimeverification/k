package org.kframework.tiny


trait Theory {
  /**
   * Tells whether the proposition is valid in this theory.
   * If we cannot find an answer (e.g., we have symbolic values), return None
   * So None means the Proposition is satisfiable.
   */
  def apply(f: Formula): Option[Boolean] = f match {
    case True => Some(true)
    case False => Some(false)
    case _ => None
  }

  def normalize(k: K): K
}

object FreeTheory extends Theory {
  override def normalize(k: K): K = {
    println(k); k
  }
}