package org.kframework.tiny.builtin

import org.kframework.attributes.Att
import org.kframework.kore.ADT.Sort
import org.kframework.tiny._
import org.kframework.tiny.matcher.{MatcherLabel, Matcher}

import scala.collection.{immutable, mutable}
import scala.collection.mutable.Builder

final class KMapApp(val klabel: KMapAppLabel, val theMap: Map[K, K], val att: Att = Att())
  extends KApp with PlainNormalization {
  val children: immutable.Iterable[K] = theMap map { case (k, v) => Tuple2Label(k, v) }
  override def matcher(right: K): Matcher = KMapAppMatcher(this, right)
}

object Tuple2Label extends RegularKAppLabel("Tuple2", Att())

case class KMapAppLabel(name: String, att: Att = Att()) extends Label {
  def constructFromFlattened(l: Map[K, K], att: Att): KMapApp = new KMapApp(this, l, att)

  def construct(l: Iterable[K], att: Att): KMapApp = {
    val b = newBuilder(att)
    l foreach b.+=
    b.result()
  }

  def newBuilder(att: Att): mutable.Builder[K, KMapApp] =
    new KMapAppBuilder(
      new mutable.MapBuilder[K, K, Map[K, K]](Map()), this).mapResult {
      constructFromFlattened(_, att)
    }
}

object KVarMapValue extends RegularKTok(Sort("KVarMapValue"), "KVarMapValue")

class KMapAppBuilder(val builder: mutable.MapBuilder[K, K, Map[K, K]], label: Label) extends Builder[K, Map[K, K]] {
  def +=(k: K): this.type = {
    k match {
      case KApp(`label`, list, att) => list map {
        case KApp(Tuple2Label, Seq(a, b), _) => (a, b)
      } foreach builder.+=

      case KApp(Tuple2Label, Seq(a, b), _) => builder += (a -> b)
      case v: KVar => builder += (v -> KVarMapValue)
    }
    this
  }

  def clear(): Unit = builder.clear()

  def result(): Map[K, K] = builder.result();
}

case class MapKeys(k: K, att: Att = Att()) extends KProduct {
  override val klabel = MapKeys
  override def toString = "keys(" + k + ")"

  override def normalizeInner(implicit theory: Theory) = ???
}

object MapKeys extends KProduct1Label with EmptyAtt {
  val name: String = "keys"
}

case class KMapAppMatcher(left: KMapApp, right: K) extends Matcher {
  override val klabel = KMapAppMatcher

  override def normalizeInner(implicit theory: Theory): K = (left.normalize, right.normalize) match {
    case (left: KMapApp, right: KMapApp) =>
      val leftGroundKeys = left.theMap.keys filter theory.isGround toSet
      val rightGroundKeys = right.theMap.keys filter theory.isGround toSet

      if ((leftGroundKeys &~ rightGroundKeys) != Set())
        False
      else
        this
    case _ => this
  }
}

object KMapAppMatcher extends MatcherLabel {
  override def apply(k1: K, k2: K, att: Att): KProduct = KMapAppMatcher(k1.asInstanceOf[KMapApp], k2)
}