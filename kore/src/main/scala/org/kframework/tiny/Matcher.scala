package org.kframework.tiny

import org.kframework.attributes.Att

trait Matcher extends KProduct with EmptyAtt {
  def left: K
  def right: K

  /** Estimate the time it takes to solve one variable */
  def estimate(implicit t: Theory): Int = ???
  /** Solve one variable */
  def step(implicit t: Theory): Or = ???

  override def att: Att = Att()
  override def klabel: MatcherLabel
}

trait MatcherLabel extends KRegularAppLabel with EmptyAtt with KProduct2Label {
  override def name: String = this.toString
}

case class KRegularAppMatcher(left: KRegularApp, right: K) extends Matcher {
  def klabel = KRegularAppMatcher


  def matchContents(ksL: Seq[K], ksR: Seq[K])(implicit theory: Theory): K =
    And(ksL.zip(ksR) map { case (k1, k2) => k1.matcher(k2) }: _*)

  override def normalize(implicit theory: Theory): K =
    (left, right) match {
      case (KApp(labelVariable: KVar, contentsP, _), KApp(label2, contents, _)) =>
        And(Binding(labelVariable, InjectedLabel(label2, Att())), matchContents(contentsP, contents))
      case (KApp(label, contentsP, att), KApp(label2, contents, att2)) if label == label2 =>
        And(matchContents(contentsP, contents))
      case _ => False
    }
}

object KRegularAppMatcher extends MatcherLabel {
  override def apply(k1: K, k2: K, att: Att): KRegularAppMatcher =
    KRegularAppMatcher(k1.asInstanceOf[KRegularApp], k2)
}


case class KVarMatcher(left: KVar, right: K) extends Matcher {
  def klabel = KVarMatcher

  override def normalize(implicit theory: Theory): K =
    Binding(left, right)
}

object KVarMatcher extends MatcherLabel with KProduct2Label {
  override def apply(k1: K, k2: K, att: Att): KVarMatcher = new KVarMatcher(k1.asInstanceOf[KVar], k2)
}

//      case (_, headP +: tailP) =>
//        (0 to klist.size)
//          .map { index => (klist.delegate.take(index), klist.delegate.drop(index)) }
//          .map {
//          case (List(oneElement), suffix) =>
//            headP.matchAll(oneElement) and tailP.matchAll(suffix)
//          case (prefix, suffix) =>
//            headP.matchAll(InjectedKList(prefix)) and tailP.matchAll(suffix)
//        }
//          .fold(False)({ (a, b) => a or b })
//      case other => False