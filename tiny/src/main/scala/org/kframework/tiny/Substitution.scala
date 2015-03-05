package org.kframework.tiny

import org.kframework.tiny.builtin.{Tuple2Label, KMapApp, KVarMapValue}
import org.kframework.tiny.matcher.Anywhere

object Substitution {
  implicit def apply(self: K): Substitution = new Substitution(self)
}

class Substitution(self: K) {

  import org.kframework.tiny.Substitution._

  def substitute(substitution: Map[KVar, K]): K = {
    doSubstitution(substitution)
  }

  private def doSubstitution(substitution: Map[KVar, K]) =
    self match {
      case v: KVar => substitution.get(v) map { _.substitute(substitution) } getOrElse v
      case Anywhere(l, p, _) => substitution(l.TOPVariable).substitute(substitution + (l.HOLEVariable -> p))
      case b: Binding => b.klabel(b.variable, b.value.substitute(substitution))
      case k: KMapApp =>
        val newChildren = k.children map {
          case KApp(Tuple2Label, Seq(k: KVar, KVarMapValue), _) =>
            substitution.get(k).getOrElse(Tuple2Label(k, KVarMapValue))
          case KApp(Tuple2Label, Seq(k, v), _) =>
            Tuple2Label(k.substitute(substitution), v.substitute(substitution))
        }

        k.klabel(newChildren.toSeq: _*)
      case KApp(l, ks, att) =>
        l(ks map { x: K => x.substitute(substitution) }, att)
      case e => e
    }
}
