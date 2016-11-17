package org.kframework.kore

import org.kframework.{AssocBuilder, CombinerFromBuilder, Collector, attributes}
import org.kframework.attributes.Att

import scala.collection.mutable.ListBuffer
import collection.JavaConverters._
import collection._

/**
 *
 * Basic implementation of a Constructor of inner KORE classes.
 * It can be used by either creating a KORE object, or by importing
 * the class statically.
 *
 * See the wiki for more details:
 * https://github.com/kframework/k/wiki/KORE-data-structures-guide
 *
 */
object KORE extends Constructors[K] with ScalaSugared[K] {
  val c = KORE

  val constructor = this

  lazy val Att = attributes.Att()

  def Location(startLine: Int, startColumn: Int, endLine: Int, endColumn: Int) = attributes.Location(startLine,
    startColumn, endLine, endColumn)

  def KApply(klabel: KLabel, klist: KList): KApply = KApply(klabel, klist, Att)

  def KToken(string: String, sort: Sort): KToken = KToken(string, sort, Att)

  def KSequence(ks: java.util.List[K]): KSequence = KSequence(ks, Att)

  def KRewrite(left: K, right: K): KRewrite = KRewrite(left, right, Att)

  def KAs(pattern: K, alias: K): KAs = KAs(pattern, alias, Att)

  def InjectedKLabel(label: KLabel): InjectedKLabel = InjectedKLabel(label, Att)

  //  def toKList: Collector[K, KList] =
  //    Collector(() => new CombinerFromBuilder(KList.newBuilder()))

  //  def toKSequence: Collector[K, KSequence] =
  //    Collector(() => new CombinerFromBuilder(KSequence.newBuilder()))

  override def KLabel(name: String): KLabel = ADT.KLabel(name)

  override def KApply(klabel: KLabel, klist: KList, att: Att): KApply = ADT.KApply(klabel, klist, att)

  override def KSequence[KK <: K](items: java.util.List[KK], att: Att): KSequence = ADT.KSequence(items.asScala
    .toList, att)

  override def KVariable(name: String, att: Att): KVariable = ADT.KVariable(name, att)

  override def Sort(name: String): Sort = ADT.Sort(name)

  override def KToken(s: String, sort: Sort, att: Att): KToken = ADT.KToken(s, sort, att)

  override def KRewrite(left: K, right: K, att: Att): KRewrite = ADT.KRewrite(left, right, att)

  override def KAs(pattern: K, alias: K, att: Att): KAs = ADT.KAs(pattern, alias, att)

  override def KList[KK <: K](items: java.util.List[KK]): KList = ADT.KList(items.asScala.toList)

  def KList[KK <: K](items: List[KK]): KList = ADT.KList(items)

  override def InjectedKLabel(klabel: KLabel, att: Att): InjectedKLabel = ADT.InjectedKLabel(klabel, att)

  def toKList: Collector[K, KList] =
    Collector(() => new CombinerFromBuilder(
      new AssocBuilder[K, ADT.KList, ADT.KList](
        ListBuffer[K]().mapResult[ADT.KList](l => ADT.KList(l))))).asInstanceOf[Collector[K, KList]]

  def toKSequence: Collector[K, KSequence] =
    Collector(() => new CombinerFromBuilder(
      new AssocBuilder[K, ADT.KSequence, ADT.KSequence](
        ListBuffer[K]().mapResult[ADT.KSequence](l => ADT.KSequence(l))))).asInstanceOf[Collector[K, KSequence]]

  def self = this

  @annotation.varargs override def KApply(klabel: KLabel, items: K*): KApply = KApply(klabel, KList(items.asJava), Att)
}
