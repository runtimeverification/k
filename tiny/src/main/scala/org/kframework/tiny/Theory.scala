package org.kframework.tiny

import org.kframework.definition._
import org.kframework.meta.{Down, Up}


trait Theory {
//  def normalize(k: K): K

}

trait FreeTheory extends Theory {
  def normalize(k: K): K = k
  val self = this
}

object FreeTheory extends FreeTheory

class TheoryWithUpDown(up: Up[K], down: Down, val module: Module) extends FreeTheory {
}

case class RewriteBasedTheory(rw: K => K) extends Theory {
  def normalize(k: K): K = rw(k)
}
