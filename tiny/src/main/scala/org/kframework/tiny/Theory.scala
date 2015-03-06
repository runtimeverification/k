package org.kframework.tiny

import org.kframework.builtin.Sorts
import org.kframework.definition._
import org.kframework.meta.{Down, Up}


trait Theory {
  def normalize(k: K): K

}

trait FreeTheory extends Theory {
  def normalize(k: K): K = k
  val self = this
}

object FreeTheory extends FreeTheory

class TheoryWithUpDown(up: Up[K], down: Down, val module: Module) extends FreeTheory {
  override def normalize(k: K): K = {
    k match {
      case t: KTok => t.sort match {
        case Sorts.Bool => t.s match {
          case "true" => And()
          case "false" => Or()
        }
        case _ => t
      }
      case t => super.normalize(k)
    }
  }
}

case class RewriteBasedTheory(rw: K => K) extends Theory {
  def normalize(k: K): K = rw(k)
}
