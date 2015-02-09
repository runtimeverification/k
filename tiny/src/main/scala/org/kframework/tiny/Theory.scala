package org.kframework.tiny

import org.kframework.tiny.matcher.EqualsMatcher


trait Theory {
  def normalize(k: K): K
  def equals(left: K, right: K) = normalize(EqualsMatcher(left, right))
  //  def deepNormalize(k: K): K = k match {
  //    case KApp(label, children, att) =>
  //      normalize(label(children map deepNormalize, att).normalize(this)) // normalization inside the label apply
  //    case l: KLeaf => normalize(l)
  //  }
}

object FreeTheory extends Theory {
  def normalize(k: K): K = k match {
    case EqualsMatcher(a, b) => if (a == b) True else False
    case t => t
  }
  val self = this
}

case class RewriteBasedTheory(rw: K => K) extends Theory {
  def normalize(k: K): K = rw(k)
}
