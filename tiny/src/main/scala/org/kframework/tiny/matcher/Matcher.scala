package org.kframework.tiny.matcher

import org.kframework.attributes.Att
import org.kframework.tiny._

trait Matcher extends KProduct with EmptyAtt {
  def left: K
  def right: K

  /** Estimate the time it takes to solve one variable */
  def estimate(implicit t: Theory): Int = ???
  /** Solve one variable */
  def step(implicit t: Theory): Or = ???

  override def att: Att = Att()
  val klabel: MatcherLabel

  override def toString = left + ":=" + right
}

trait MatcherLabel extends KRegularAppLabel with EmptyAtt with KProduct2Label {
  override def name: String = this.getClass.toString
}

trait KAppMatcher extends Matcher {
  def matchContents(ksL: Seq[K], ksR: Seq[K])(implicit theory: Theory): K

  override def normalizeInner(implicit theory: Theory): K = {
    val x = (left.normalize, right.normalize) match {
      case (KApp(labelVariable: KVar, contentsP, _), KApp(label2, contents, _)) =>
        And(Binding(labelVariable, InjectedLabel(label2, Att())), matchContents(contentsP, contents).normalize)
      case (KApp(label, contentsP, att), KApp(label2, contents, att2)) if label == label2 =>
        matchContents(contentsP, contents).normalize
      case (KApp(label, contentsP, att), k) if this.isInstanceOf[KAssocAppMatcher] => // ugly instanceOf
        matchContents(contentsP, Seq(k)).normalize
      case _ =>
        False
    }
    x
  }

}

case class KRegularAppMatcher(left: KRegularApp, right: K) extends KAppMatcher {
  val klabel = KRegularAppMatcher

  def matchContents(ksL: Seq[K], ksR: Seq[K])(implicit theory: Theory): K =
    And(ksL.zip(ksR) map { case (k1, k2) => k1.matcher(k2) }: _*)

  override def isFalse = (left, right) match {
    case (KApp(label, _, _), KApp(label2, _, _)) => label != label2
    case _ => false
  }
}

object KRegularAppMatcher extends MatcherLabel {
  def apply(k1: K, k2: K, att: Att): KProduct =
    KRegularAppMatcher(k1.asInstanceOf[KRegularApp], k2)
}

case class KAssocAppMatcher(left: KAssocApp, right: K) extends KAppMatcher {
  val klabel = KAssocAppMatcher

  def matchContents(ksL: Seq[K], ksR: Seq[K])(implicit theory: Theory): K = {
    val res = (ksL, ksR) match {
      case (Seq(), Seq()) => Or(True)
      case (headL +: tailL, headR +: tailR) if theory.equals(headL, headR) => matchContents(tailL, tailR)
      case (headL +: tailL, ksR) =>
        (0 to ksR.size)
          .map { index => (ksR.take(index), ksR.drop(index)) }
          .map {
          case (List(oneElement), suffix) =>
            And(headL.matcher(oneElement), matchContents(tailL, suffix))
          case (prefix, suffix) =>
            And(headL.matcher(left.klabel(prefix, right.att)), matchContents(tailL, suffix))
        }
          .fold(False)({ (a, b) => Or(a, b) })

      case other => False
    }
    res
  }

  override def isFalse = (left, right) match {
    case (KApp(label, Seq(), _), KApp(label2, Seq(), _)) => label != label2
    case _ => false
  }
}

object KAssocAppMatcher extends MatcherLabel {
  def apply(k1: K, k2: K, att: Att): KProduct =
    KAssocAppMatcher(k1.asInstanceOf[KAssocApp], k2)
}

case class KVarMatcher(left: KVar, right: K) extends Matcher {
  val klabel = KVarMatcher

  assert(!right.isInstanceOf[KVar])

  override def normalizeInner(implicit theory: Theory): K =
    Binding(left, right.normalize)

}

object KVarMatcher extends MatcherLabel with KProduct2Label {
  override def apply(k1: K, k2: K, att: Att): KProduct =
    new KVarMatcher(k1.asInstanceOf[KVar], k2)
}

case class EqualsMatcher(left: K, right: K) extends Matcher {
  override val klabel = EqualsMatcher
  override def toString = left + ":=" + right

  override protected[this] def normalizeInner(implicit theory: Theory): K = {
    val res = if (left == right)
      True
    else if (isGround && left != right)
      False
    else
      this

    res
  }
}

object EqualsMatcher extends MatcherLabel with KProduct2Label {
  override def apply(k1: K, k2: K, att: Att): KProduct =
    new EqualsMatcher(k1, k2)
}
