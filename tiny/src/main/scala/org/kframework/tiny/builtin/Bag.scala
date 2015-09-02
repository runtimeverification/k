package org.kframework.tiny.builtin

import org.kframework.attributes.Att
import org.kframework.tiny._
import org.kframework.tiny.matcher.{AssocMatchContents, KAppMatcher, Matcher, MatcherLabel}

case class Bag(klabel: BagLabel, children: collection.Bag[K], att: Att = Att()) extends KAssocApp {
  override def matcher(right: K): Matcher = BagMatcher(this, right)
}

case class BagLabel(name: String, att: Att = Att()) extends KAssocAppLabel {
  implicit val bagConfig = collection.Bag.configuration.compact[K]

  override def constructFromFlattened(l: Seq[K], att: Att): Bag = Bag(this, collection.Bag(l: _*), att)
}

case class BagMatcher(left: Bag, right: K) extends KAppMatcher with AssocMatchContents {
  override def matchContents(ksL: Seq[K], ksR: Seq[K])(implicit theory: Theory): K = {
    val groundLeft = ksL filter { _.isGround }
    val groundRight = ksR filter { _.isGround }

    if ((groundLeft diff groundRight).size > 0)
      False
    else {
      val remainingRight = ksR.toList diff groundLeft
      val symbolicLeft = ksL diff groundRight

      Or((for (oneLeft <- symbolicLeft.permutations;
               oneRight <- remainingRight.permutations) yield {
        AsOr(super[AssocMatchContents].matchContents(oneLeft, oneRight)).children
      }).flatten.toSeq: _*)
    }
  }
  override val klabel: MatcherLabel = BagMatcher
  override val leftKLabel: Label = left.klabel
  override val rightAtt: Att = right.att
}
object BagMatcher extends MatcherLabel {
  override def apply(k1: K, k2: K, att: Att): KProduct = BagMatcher(k1.asInstanceOf[Bag], k2)
}