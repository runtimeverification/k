// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.koreimplementation

import org.kframework._
import attributes._
import org.kframework.builtin.Sorts
import org.kframework.tinyimplementation._
import scala.collection.JavaConverters._
import org.kframework.kore.Sort

import scala.collection.mutable.{Builder, ListBuffer}

/* Interfaces */

sealed trait KORE

// marker for KORE final classes added as a result of a discussion with Brandon about sealing


trait K extends kore.K with Pattern {
  protected type This <: K

  def copy(att: Att): This
}

trait Node extends K {
  def transform(t: K => Option[K]): K

  def find(f: K => Boolean): Set[K]
}

trait Leaf extends Node {
  def transform(t: K => Option[K]): K =
    t.apply(this).getOrElse(this)

  def find(f: K => Boolean): Set[K] = if (f(this)) Set(this) else Set()
}

trait EmptyAttributes extends K {
  protected type This = EmptyAttributes

  def att: Att = Att()

  def copy(att: Att): This =
    if (att != Att)
      throw new UnsupportedOperationException("Att must be empty.")
    else
      this
}

trait KItem extends kore.KItem with K

trait KLabel extends kore.KLabel with KLabelToString

trait KToken extends kore.KToken with KItem with KORE with KTokenToString with KTokenPattern {
  val sort: Sort
  val s: String
}

/* Data Structures */

class KList(val delegate: List[K]) extends kore.KList with Collection[K] with Indexed[Int, K] with KListPattern with
KListToString with KORE {
  type This = KList

  override def canEqual(that: Any) = that.isInstanceOf[KList]

  def newBuilder(): Builder[K, KList] = KList.newBuilder(att)

  def get(i: Int) = delegate.lift(i)

  def att = Att()

  def copy(att: Att): KList = this

  def iterable: Iterable[K] = delegate

  def items: java.util.List[kore.K] = iterable.toList.asJava.asInstanceOf[java.util.List[kore.K]]

  override def size = items.size
}

trait KApply extends kore.KApply with KCollection {
  def klabel: KLabel

  def klist: KList

  override def size = klist.size
}

object KApply {
  def apply(klabel: KLabel, klist: KList, att: Att = Att()) = {
    KSimpleApply(klabel, klist, att)
  }

  def unapply(kapply: KApply): Option[(KLabel, KList, Att)] = kapply match {
    case KSimpleApply(klabel, klist, att) => Some((klabel, klist, att))
    case _ => ???
  }
}

case class KSimpleApply(val klabel: KLabel, val klist: KList, val att: Att = Att())
  extends KApply with KAbstractCollection with Indexed[Int, K]
  with KApplyPattern with Associative[KList]
  with KApplyToString with KORE {
  type This = KSimpleApply

  protected[koreimplementation] def delegate: Iterable[K] = klist.delegate

  def get(i: Int) = klist.get(i)

  def newBuilder: Builder[K, KSimpleApply] = klist.newBuilder() mapResult { new KSimpleApply(klabel, _, att) }

  override def canEqual(that: Any) = that match {
    case t: KApply => t.klabel == klabel
    case _ => false
  }

  override def copy(att: Att): This = KApply(klabel, klist, att)
}

case class KUninterpretedToken(sort: Sort, s: String, override val att: Att = Att())
  extends KToken with KTokenToString with KORE with Leaf {
  type This = KToken

  def copy(att: Att): KToken = new KUninterpretedToken(sort, s, att)
}

case class ConcreteKLabel(name: String) extends KLabel with KORE {
  def apply(ks: K*) = KApply(this, KList(ks))

  def apply(ks: List[K]) = KApply(this, KList(ks))
}

case class KSequence(val ks: List[K], val att: Att = Att())
  extends kore.KSequence with KAbstractCollection with KSequencePattern with KSequenceToString with KORE {
  type This = KSequence

  def delegate = ks

  def newBuilder(): Builder[K, KSequence] = KSequence.newBuilder(att)

  def copy(att: Att): KSequence = new KSequence(ks, att)

  def canEqual(that: Any) = that.isInstanceOf[KSequence]

  override def size = items.size

  def items: java.util.List[kore.K] = delegate.asJava.asInstanceOf[java.util.List[kore.K]]
}

case class KVariable(name: String, att: Att = Att())
  extends kore.KVariable with KItem with KORE with KLabel with KVariablePattern with KVariableToString with Leaf {
  type This = KVariable

  def copy(att: Att): KVariable = new KVariable(name, att)
}

case class KRewrite(left: K, right: K, att: Att = Att())
  extends kore.KRewrite with KAbstractCollection with KORE with KRewritePattern with KRewriteToString {
  type This = KRewrite

  def copy(att: Att): KRewrite = new KRewrite(left, right, att)

  val klist = KList(left, right)

  protected[koreimplementation] def delegate: Iterable[K] = Seq(left, right)

  def newBuilder: Builder[K, KRewrite] = ListBuffer[K]() mapResult {
    case List(left, right) => KRewrite(left, right)
  }
}

case class InjectedKLabel(klabel: KLabel) extends KItem with InjectedKLabelPattern with Leaf with kore.InjectedKLabel {
  type This = InjectedKLabel

  def att() = Att()

  def copy(att: Att) = this

  override def toString = "#klabel" + "(" + klabel + ")";
}

case class InjectedKList(klist: KList, att: Att = Att()) extends KAbstractCollection
with InjectedKListPattern {
  type This = InjectedKList

  def copy(att: Att) = InjectedKList(klist, att)

  def delegate = klist.delegate

  override def toString = "#klist" + "(" + klist + ")";

  def newBuilder(): Builder[K, InjectedKList] = InjectedKList.newBuilder(att)
}

object InjectedKList extends CanBuildKCollection {
  type This = InjectedKList

  def newBuilder(att: Att = Att()) =
    new AssocBuilder[K, KList, InjectedKList](KList.newBuilder(att))
      .mapResult { new InjectedKList(_, att) }

  def flattenKList(l: KList): KList =
    KList(l map { x: Any =>
      x match {
        case il: InjectedKList => il.klist.iterator
        case x: K => List(x)
      }
    } flatten)
}

/*  Constructors */

object KList {
  type This = KList

  def apply(l: Iterable[K]): KList = (newBuilder() ++= l).result()

  def newBuilder(att: Att = Att()): Builder[K, KList] =
    new AssocBuilder[K, List[K], KList](ListBuffer()) mapResult { new KList(_) }

  def unapplySeq(l: KList): Option[Seq[K]] = Some(l.delegate.toSeq)

  def apply(l: K*): This = (canBuildFrom.apply() ++= l).result

  protected val fromList = apply _

  import scala.collection._

  implicit def canBuildFrom: generic.CanBuildFrom[This, K, This] =
    new generic.CanBuildFrom[This, K, This] {
      def apply(): mutable.Builder[K, This] = newBuilder()

      def apply(from: This): mutable.Builder[K, This] = from.newBuilder.asInstanceOf[Builder[K, This]]
    }
}

object KToken {
  def apply(sort: Sort, s: String, att: Att = Att()) =
    KUninterpretedToken(sort, s, att)

  def apply(sort: Sort, s: String) =
    KUninterpretedToken(sort, s, Att())

  def unapply(t: KToken) = Some((t.sort, t.s, t.att))

  implicit def from(i: Int) = apply(Sorts.Int, i.toString)

  implicit def from(s: String) = apply(Sorts.KString, s)
}

object KVariable {
  val it = this
}

object KSequence extends CanBuildKCollection {
  type This = KSequence

  def newBuilder(att: Att = Att()) =
    new AssocBuilder[K, List[K], KSequence](ListBuffer())
      .mapResult { new KSequence(_, att) }
}

object KRewrite {
  def apply(klist: KList, att: Att): KRewrite = klist match {
    case KList(left, right) => new KRewrite(left, right, att)
  }

  def apply(list: K*): KRewrite = apply(KList(list: _*), Att())
}

object EmptyK {
  def apply() = KSequence(List(), Att())
}

object KLabel extends ConcreteKLabel("KLabel") {
  def apply(name: String) = ConcreteKLabel(name)

  def unapply(klabel: ConcreteKLabel): Option[String] = Some(klabel.name)
}

/* Constructors for matching KORE */

object KLabelWithQuotes {
  def apply(s: String) = {
    KLabel(s.stripPrefix("`").stripSuffix("`"))
  }
}

object KORE {
  implicit def seqOfKsToKList(ks: Seq[K]) = KList(ks: _*)

  implicit def SymbolToKLabel(s: Symbol) = KLabel(s.name)

  implicit def StringToKToken(s: String) = KToken(Sorts.KString, s)
}

object UglyHack {
  implicit def toNode(k: K): Node = k.asInstanceOf[Node]
}
