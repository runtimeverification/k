package org.kframework.tiny

import java.util.concurrent.Callable

import org.kframework._
import org.kframework.attributes.Att
import org.kframework.builtin.Sorts
import org.kframework.kore.ADT
import org.kframework.tiny.matcher._

import scala.collection.JavaConverters._
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

//////////////////
//   TRAITS
//////////////////


trait K extends kore.K {
  def att: Att

  def matcher(right: K): Matcher

  val outerThis = this

  final def normalize(implicit theory: Theory): K = {
    if (this.normalBy.contains(theory)) {
      this
    } else {
      val res = theory.cache.get(this, new Callable[K] {
        override def call(): K = {
          var finalRes: K = null
          var inner: K = outerThis
          do {
            //            println(inner + " ..... " + finalRes)
            finalRes = inner
            inner = inner.normalizeInner
            inner = theory.normalize(inner)
          } while (finalRes != inner)
          //          println(" ... => " + finalRes)
          finalRes.normalBy.+=(theory)
          finalRes
        }
      })
      res
    }
  }

  def normalizeInner(implicit theory: Theory): K

  def isGround: Boolean

  private val normalBy = collection.mutable.Set[Theory]()

  def isNormalBy(theory: Theory) = normalBy.contains(theory)
  def setIsNormalBy(theory: Theory) = normalBy.+=(theory)

  def isFalse: Boolean = false
}

object KApp {
  def unapply(k: KApp): Option[(Label, Seq[K], Att)] = Some(k.klabel, k.children.toSeq, k.att)
}

/**
 * Term with children. We automatically lift KSeq and KRewrite to KApp.
 */
trait KApp extends {} with kore.KApply with K {
  // KApp seen as a collection Set(2, Set(3, 4)) is normalized and has size 3 and 2,3,4 as children
  def size: Int = children.size

  def asIterable = new org.kframework.List[kore.K](children.toList)

  def items = children.toList.asJava.asInstanceOf[java.util.List[kore.K]]

  def children: Iterable[K]

  lazy val isGround = !(children exists {
    !_.isGround
  })

  val klabel: Label

  // The KApp seen as a KApply -- Set(2, Set(3, 4)) is normalized, but klist = KList(2, Set(3, 4))
  def klist = kore.KORE.KList(children.asInstanceOf[Iterable[kore.K]].toSeq.asJava)

  override def equals(that: Any) =
    hashCode == that.hashCode && (that match {
      case that: AnyRef if that.asInstanceOf[AnyRef] eq this => true
      case that: KApp =>
        that.klabel == klabel && this.children == that.children
      case _ => false
    })


  override def computeHashCode = klabel.hashCode * 5333 + children.hashCode

  override def toString = klabel + "(" + children.mkString(",") + ")"
}

trait PlainNormalization {
  self: KApp =>
  def normalizeInner(implicit theory: Theory): K =
    klabel((children map {
      _.normalize
    }).toSeq, att)
}

/**
 * Term without children.
 */
trait KLeaf extends K {
  def copy(att: Att): KLeaf

  def normalizeInner(implicit theory: Theory): K = this

  override def isNormalBy(theory: Theory) = true
}

/**
 * KApp with a collection of children which are usually defined using an associative operator.
 */
trait KAssocApp extends KApp with PlainNormalization {
  val klabel: KAssocAppLabel

  def head: K = children.head

  def tail: K = klabel.construct(children.tail, att)

  def map(f: K => K): K = klabel.construct(children.map(f), att)

  override def matcher(right: K): Matcher = KAssocAppMatcher(this, right)
}

trait KRegularApp extends KApp {
  val klabel: KRegularAppLabel

  override def matcher(other: K): Matcher = KRegularAppMatcher(this, other)
}

/**
 * KApp with fixed arity. It is defined using a non-associative operator.
 */
trait KProduct extends KRegularApp with Product {
  val children = productIterator collect { case k: K => k } toList
}

/**
 * KToken-like term, i.e. term without children representing a constant value.
 * KSimpleTok is one example. KInt is another.
 */
trait KTok extends kore.KToken with KLeaf {
  override def matcher(right: K): Matcher = EqualsMatcher(this, right)

  val isGround = true
}

trait EmptyAtt {
  def att = Att()
}

///////////////////
//   CLASSES
///////////////////

case class KVar(name: String, att: Att = Att()) extends kore.KVariable with KLeaf {
  def copy(att: Att): KVar = KVar(name, att)

  override def matcher(right: K): Matcher = KVarMatcher(this, right)

  override def toString = name

  lazy val isGround = false
}

case class RegularKTok(sort: Sort, s: String, att: Att = Att()) extends KTok {
  def copy(att: Att): RegularKTok = RegularKTok(sort, s, att)

  override def toString = s + ":" + sort
}

case class TypedKTok[T](sort: Sort, nativeValue: T, att: Att = Att()) extends KTok {
  override def copy(att: Att): KLeaf = TypedKTok(sort, nativeValue, att)

  override def s: String = nativeValue.toString

  override def toString = nativeValue.toString
}

case class NativeBinaryOp[A, B, R](val klabel: NativeBinaryOpLabel[A, B, R], val children: Seq[K], val att: Att = Att())
  extends KRegularApp with PlainNormalization {

  if (children.head == And())
    ???

  override def normalizeInner(implicit theory: Theory): K =
    super[PlainNormalization].normalizeInner match {
      case KApp(l, Seq(TypedKTok(s1, v1, _), TypedKTok(s2, v2, _)), _) =>
        try {
          val res = klabel.f(v1.asInstanceOf[A], v2.asInstanceOf[B])
          TypedKTok(klabel.resSort, res)
        } catch {
          case e: ArithmeticException => False
        }
      case x: KApp => x
    }
}

case class NativeUnaryOp[T, R](val klabel: NativeUnaryOpLabel[T, R], val children: Seq[K], val att: Att = Att())
  extends KRegularApp with PlainNormalization {
  override def normalizeInner(implicit theory: Theory): K =
    super[PlainNormalization].normalizeInner match {
      case KApp(l, Seq(TypedKTok(s, v, _)), _) => TypedKTok(klabel.resSort, klabel.f(v.asInstanceOf[T]))
      case x => x
    }
}

case class UnaryHookedFunction(klabel: UnaryHookedFunctionLabel, val children: Seq[K], val att: Att = Att())
  extends KRegularApp with PlainNormalization {
  override def normalizeInner(implicit theory: Theory): K = {
    val normalizedChildren = super[PlainNormalization].normalizeInner.asInstanceOf[KApp]
    klabel.f.lift.apply(normalizedChildren.children.head).getOrElse(normalizedChildren)
  }
}

case class BinaryHookedFunction(klabel: BinaryHookedFunctionLabel, val children: Seq[K], val att: Att = Att())
  extends KRegularApp with PlainNormalization {
  override def normalizeInner(implicit theory: Theory): K = {
    val normalizedChildren = super[PlainNormalization].normalizeInner.asInstanceOf[KApp]
    klabel.f.lift.apply(normalizedChildren.children.head, normalizedChildren.children.tail.head).getOrElse(normalizedChildren)
  }
}

final class RegularKApp(val klabel: RegularKAppLabel, val children: Seq[K], val att: Att = Att())
  extends KRegularApp with PlainNormalization

final class RegularKAssocApp(val klabel: KAssocAppLabel, val children: Seq[K], val att: Att = Att())
  extends KAssocApp

final class KSeq private(val children: Seq[K], val att: Att)
  extends kore.KSequence with KAssocApp with PlainNormalization {
  val klabel = KSeq

  override def computeHashCode = super[KAssocApp].computeHashCode
}

case class KRewrite(val left: K, val right: K, val att: Att = Att()) extends
kore.KRewrite with KProduct with PlainNormalization {
  val klabel = KRewrite
}

case class InjectedLabel(klabel: Label, att: Att) extends kore.InjectedKLabel with KTok {
  override def copy(att: Att): KLeaf = InjectedLabel(klabel, att)

  val sort: Sort = InjectedLabel.sort
  val s: String = klabel.toString

  override def computeHashCode = super[InjectedKLabel].computeHashCode
}

object InjectedLabel {
  val sort = ADT.Sort("InjectedKLabel")
}

/////////////////////
//   LABEL TRAITS
/////////////////////

trait Label extends kore.KLabel {
  def apply(l: Seq[K], att: Att): K =
    construct(l, att)

  def construct(l: Iterable[K], att: Att): K

  @annotation.varargs def apply(l: K*): K = apply(l, Att())

  def att: Att

  override def toString = name

  override def equals(that: Any) = super.equals(that)
}

trait KRegularAppLabel extends Label {

}

trait KProduct1Label extends KRegularAppLabel {
  def apply(k: K, att: Att): KProduct

  def construct(l: Iterable[K], att: Att): KProduct =
    l match {
      case Seq(k) => apply(k, att)
    }
}

trait KProduct2Label extends KRegularAppLabel {
  def apply(k1: K, k2: K, att: Att): KProduct

  def construct(l: Iterable[K], att: Att): KProduct =
    l match {
      case Seq(k1, k2) => apply(k1, k2, att)
    }
}

case class LiftBoolToML(k: K, val att: Att = Att()) extends KProduct {
  val klabel = LiftBoolToMLLabel

  override def normalizeInner(implicit theory: Theory): K = {
    k.normalize match {
      case TypedKTok(Sorts.Bool, true, _) => And()
      case TypedKTok(Sorts.Bool, false, _) => Or()
      case x => LiftBoolToML(x)
    }
  }
}


trait KAssocAppLabel extends Label {
  def construct(l: Iterable[K], att: Att): K =
    if (l.size == 1)
      return l.head
    else {
      val b = newBuilder(att)
      l foreach b.+=
      b.result()
    }

  def newBuilder(att: Att): mutable.Builder[K, KAssocApp] =
    new KAppAssocBuilder(ListBuffer[K](), this).mapResult {
      constructFromFlattened(_, att)
    }

  def constructFromFlattened(l: Seq[K], att: Att): KAssocApp
}


///////////////
//   LABELS
///////////////

object KRewrite extends KRegularAppLabel {
  val att = Att()
  val name = "=>"

  def construct(l: Iterable[K], att: Att): KRewrite =
    l match {
      case Seq(left, right) => new KRewrite(left, right, att)
    }
}

case class RegularKAppLabel(name: String, att: Att) extends KRegularAppLabel {
  override def construct(l: Iterable[K], att: Att): RegularKApp = new RegularKApp(this, l.toSeq, att)
}

case class UnaryHookedFunctionLabel(name: String, att: Att, f: PartialFunction[K, K]) extends KRegularAppLabel {
  override def construct(l: Iterable[K], att: Att): UnaryHookedFunction = new UnaryHookedFunction(this, l.toSeq, att)
}

case class BinaryHookedFunctionLabel(name: String, att: Att, f: PartialFunction[(K, K), K]) extends KRegularAppLabel {
  override def construct(l: Iterable[K], att: Att): BinaryHookedFunction = new BinaryHookedFunction(this, l.toSeq, att)
}

case class NativeBinaryOpLabel[A, B, R](name: String, att: Att, f: (A, B) => R, resSort: Sort) extends KRegularAppLabel {
  override def construct(l: Iterable[K], att: Att): NativeBinaryOp[A, B, R] = new NativeBinaryOp(this, l.toSeq, att)
}

case class NativeUnaryOpLabel[T, R](name: String, att: Att, f: T => R, resSort: Sort) extends KRegularAppLabel {
  override def construct(l: Iterable[K], att: Att): NativeUnaryOp[T, R] = new NativeUnaryOp(this, l.toSeq, att)
}

case class RegularKAssocAppLabel(name: String, att: Att) extends KAssocAppLabel {
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new RegularKAssocApp(this, l, att)
}

object KSeq extends {
  val name = "#KSequence";
  val att = Att()
} with KAssocAppLabel {
  /* required */
  override def constructFromFlattened(l: Seq[K], att: Att): KAssocApp = new KSeq(l, att)
}


object LiftBoolToMLLabel extends KProduct1Label {

  override def apply(k: K, att: Att): KProduct = LiftBoolToML(k, att)

  override def att: Att = Att()

  override def name: String = "LiftBoolToMLLabel"
}
