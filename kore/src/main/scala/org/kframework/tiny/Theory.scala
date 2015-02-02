package org.kframework.tiny


trait Theory {
  def normalize(k: K): K
}

object FreeTheory extends Theory {
  override def normalize(k: K): K = k
}

case class RewriteBasedTheory(rw: K => K) extends Theory {
  override def normalize(k: K): K = rw(k)
}
