package org.kframework.tiny.matcher

import org.kframework.attributes.Att
import org.kframework.tiny._


case class Anywhere(klabel: AnywhereLabel, k: K, att: Att = Att()) extends KProduct with PlainNormalization {
  override def matcher(right: K): Matcher = AnywhereMatcher(this, right)
  val TOPVariable = klabel.TOPVariable
  val HOLEVariable = klabel.HOLEVariable
}

object Anywhere {
  def apply(name: String, k: K): Anywhere = AnywhereLabel(name)(k, Att())
}

case class AnywhereLabel(name: String) extends KProduct1Label with EmptyAtt {
  def apply(k: K, att: Att): Anywhere = new Anywhere(this, k, att)

  val TOPVariable = KVar(name + ".TOPVariable", Att())
  val HOLEVariable = KVar(name + ".HOLEVariable", Att())
}

case class AnywhereMatcher(left: Anywhere, right: K) extends Matcher with KProduct {
  override val klabel = AnywhereMatcher
  val TOPVariable = left.TOPVariable
  val HOLEVariable = left.HOLEVariable

  override def normalizeInner(implicit theory: Theory) = {
    val localSolution = And(left.k.matcher(right), Binding(TOPVariable, HOLEVariable))
    val childrenSolutions = right match {
      case k: KApp =>
        Or(k.children.map { c: K => // we are generating distinct solutions for each child of the right
          val solution: K = left.matcher(c).normalize
          val updatedSolution: K = solution match {
            case orSolution: Or => Or(orSolution.children map {
              case s: And => // for each distinct subsolution (a child c may have multiple subsolutions)
                rewire(s, k, c)
            } toSeq: _*)
          }
          updatedSolution
        }.toSeq: _*)
      case _ => False
    }
    Or(localSolution, childrenSolutions).normalize
  }

  private def rewire(toRewire: And, k: KApp, childOfK: K)(implicit theory: Theory): K = {
    val newAnywhere: K = k.klabel(k.children map { childK: K =>
      childK match {
        case `childOfK` => toRewire.binding(TOPVariable)
        case t: K => t
      }
    } toSeq, k.att)
    val anywhereWrapper = Binding(TOPVariable, newAnywhere)
    val newChildren = toRewire.children.map {
      case b: Binding if b.variable == TOPVariable => anywhereWrapper
      case x => x
    }
    And(newChildren.toSeq: _*).normalize
  }

}

object AnywhereMatcher extends MatcherLabel with KProduct2Label {
  override def apply(k1: K, k2: K, att: Att): KProduct =
    new AnywhereMatcher(k1.asInstanceOf[Anywhere], k2)
}

