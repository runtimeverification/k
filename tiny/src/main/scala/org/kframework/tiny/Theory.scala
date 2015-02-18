package org.kframework.tiny

import org.kframework.meta.{Up, Down}
import org.kframework.tiny.matcher.EqualsMatcher


trait Theory {
  def normalize(k: K): K
  def equals(left: K, right: K) = normalize(EqualsMatcher(left, right))
  //  def deepNormalize(k: K): K = k match {
  //    case KApp(label, children, att) =>
  //      normalize(label(children map deepNormalize, att).normalize(this)) // normalization inside the label apply
  //    case l: KLeaf => normalize(l)
  //  }

  def isGround(k: K): Boolean = k match {
    case KApp(label, children, _) => !(children exists { !isGround(_) })
    case x: KVar => false
    case _ => true
  }
}

trait FreeTheory extends Theory {
  def normalize(k: K): K = k match {
    case EqualsMatcher(a, b) if a == b =>
      True
    case m@EqualsMatcher(a, b) if isGround(m) && a != b =>
      False
    case t => t
  }
  val self = this
}

object FreeTheory extends FreeTheory

class TheoryWithUpDown(up: Up, down: Down) extends FreeTheory {
  override def normalize(k: K): K = {
    k match {
      case KApp(RegularKAppLabel("isKResult", _), _, _) =>
        True
      case t =>
        try {
          up(down(t)).asInstanceOf[K]
        } catch {
          case e => super.normalize(k)
        }
    }
  }
}

case class RewriteBasedTheory(rw: K => K) extends Theory {
  def normalize(k: K): K = rw(k)
}
