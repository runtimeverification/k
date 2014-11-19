package org.kframework.kore

import KBoolean._
import KORE._

trait Rewriting {
  self: K =>
  /**
   * rewrite using the rewrite rule in K
   */
  def rewrite(rewrite: KRewrite): Some[K] = {
    ???
  }

  /**
   * search using the rewrite rule in K
   */
  def search(rewrite: KRewrite): Set[K] = {
    val solutions = matchAll(rewrite.left, true)

    solutions map { substituion => rewrite.right.transform(substituion) }
  }

  def transform(substituion: Map[KVariable, K]): K = this match {
    case v: KVariable => substituion.getOrElse(v, v)
    case c: KCollection with K =>
      val newChildren = c map { _.transform(substituion) }
      c.copy(KList(newChildren.toSeq: _*))
    case e => e
  }
}
