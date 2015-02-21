package org.kframework.tiny

import org.kframework.builtin.Sorts
import org.kframework.kore.Unapply
import org.kframework.meta.{Up, Down}
import org.kframework.tiny.matcher.EqualsMatcher
import org.kframework.definition._


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

class TheoryWithUpDown(up: Up, down: Down, module: Module) extends FreeTheory {
  override def normalize(k: K): K = {
    k match {
      case SortPredicate(SortPredicateLabel(s), kk, _) if !kk.isInstanceOf[KVar] =>
        val actualSort = kk match {
          case KApp(l, _, _) => module.sortFor(l)
          case Unapply.KToken(s, _) => s
        }
        if (module.subsorts.<(actualSort, s)) True else False

      case t: KTok => t.sort match {
        case Sorts.KBoolean => t.s match {
          case "true" => And()
          case "false" => Or()
        }
        case _ => t
      }
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
