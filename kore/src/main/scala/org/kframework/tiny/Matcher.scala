package org.kframework.tiny

import org.kframework.attributes.Att

trait Matcher extends KProduct {
  def left: K
  def right: K

  /** Estimate the time it takes to solve one variable */
  def estimate(implicit t: Theory): Int = ???
  /** Solve one variable */
  def step(implicit t: Theory): Or = ???

  override def att: Att = Att()
//  override def klabel: Label = Matcher
}

//object Matcher extends Label {
//  override def construct(l: Iterable[K], att: Att): Matcher = l match {case Seq(a, b) => Matcher(a, b) }
//  val att: Att = Att()
//  val name: String = "Matcher"
//}

//case class KAppMatcher {
//  def m(p: K, k: K)(implicit theory: Theory): Or = {
//    (p, k) match {
//      case (KApp(labelVariable: KVar, contentsP, _), KApp(label2, contents, _)) =>
//        Or(And(Binding(labelVariable, InjectedLabel(label2, Att()))), And(contentsP.matcher(contents)))
//      case (KApp(label, contentsP, att), KApp(label2, contents, att2)) if label == label2 =>
//        Or(And(Matcher(contentsP, contents)))
//      case _ => False
//    }
//  }
//}
