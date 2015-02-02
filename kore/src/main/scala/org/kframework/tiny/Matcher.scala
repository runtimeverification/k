package org.kframework.tiny

import org.kframework.attributes.Att

case class Matcher(a: K, b: K) extends Formula {
  /** Estimate the time it takes to solve one variable */
  def estimate(implicit t: Theory): Int = ???
  /** Solve one variable */
  def step(implicit t: Theory): Or = ???
}

case class KAppPattern {
  def m(p: K, k: K)(implicit theory: Theory): Or = {
    (p, k) match {
      case (KApp(labelVariable: KVar, contentsP, _), KApp(label2, contents, _)) =>
        Or(And(Binding(labelVariable, InjectedLabel(label2, Att()))), And(Matcher(contentsP, contents)))
      case (KApp(label, contentsP, att), KApp(label2, contents, att2)) if label == label2 =>
        Or(And(Matcher(contentsP, contents)))
      case _ => False
    }
  }
}
