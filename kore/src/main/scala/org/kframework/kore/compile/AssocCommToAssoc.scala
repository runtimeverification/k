package org.kframework.kore.compile

import org.kframework.attributes.Att
import org.kframework.builtin.KLabels
import org.kframework.definition.{Module, Rule, Sentence}
import org.kframework.kore.SortedADT.SortedKVariable
import org.kframework.kore._


/**
 * Compiler pass for merging the rules as expected by FastRuleMatcher
 */
class AssocCommToAssoc(c: Constructors[K]) extends (Module => Module) {

  import c._

  val s = new ScalaSugar(c)

  import s._

  val rwLabel: KLabel = KLabel(KLabels.KREWRITE)

  override def apply(m: Module): Module = {
    Module(m.name, m.imports, m.localSentences flatMap {apply(_)(m)}, m.att)
  }

  def apply(s: Sentence)(implicit m: Module): List[Sentence] = {
    s match {
      case r: Rule => apply(r.body) map {Rule(_, r.requires, r.ensures, r.att)}
      case _ => List(s)
    }
  }

  def apply(k: K)(implicit m: Module): List[K] = {
    k match {
      case kApply: KApply => convert(kApply) flatMap {
        case Unapply.KApply(label: KLabel, children: List[K]) =>
          crossProduct(children map apply) map {label(_: _*)}
      }
      case Unapply.KRewrite(left, right) => apply(left) map {KRewrite(_, right, Att())}
      case _ => List(k)
    }
  }

  def crossProduct[T](lls: List[List[T]]): List[List[T]] = {
    lls match {
      case (head: List[T]) :: (tail: List[List[T]]) =>
        for {(x: T) <- head; (xs: List[T]) <- crossProduct(tail)} yield x :: xs
      case List() => List()
    }
  }

  def convert(kApply: KApply)(implicit m: Module): List[K] = {
    val att: Att = m.attributesFor.getOrElse(kApply.klabel, Att())
    if (att.contains(Att.assoc) && att.contains(Att.comm)) {
      assert(att.contains(Att.bag))
      val opKLabel: KLabel = kApply.klabel
      val unitKLabel: KLabel = KLabel(m.attributesFor(opKLabel).get(Att.unit).get)
      val opSort: Sort = m.signatureFor(opKLabel).head._2
      val unitK: K = unitKLabel()

      val (flatLHS: List[K], flatRewrites: List[K]) = flatten(kApply, kApply.klabel, unitKLabel)
      val (flatLHSElements: List[K], flatLHSCollections: List[K]) = flatLHS partition {
        case v: SortedKVariable => m.subsorts.lessThanEq(v.sort, opSort);
        case _ => true
      }

      assert(flatLHSCollections forall { case v: KVariable => v.name.equals("THE_VARIABLE") })

      val convertedLHSs: List[List[K]] = if (flatLHSCollections.nonEmpty) {
        flatLHSElements.permutations.toList map {
          _.foldRight(List(anonymousVariable(opSort))) { (e, l) => e :: anonymousVariable(opSort) :: l }
        }
      } else {
        flatLHSElements.permutations.toList
      }

      val convertedRHS: List[K] = flatRewrites map {KRewrite(unitK, _, Att())}

      convertedLHSs map (l => opKLabel(l ++ convertedRHS: _*))
    } else {
      List(kApply)
    }
  }

  def flatten(k: K, op: KLabel, unit: KLabel): (List[K], List[K]) = {
    k match {
      case Unapply.KApply(`op`, children: List[K]) =>
        children
          .map {flatten(_, op, unit)}
          .reduce { (a, b) => (a._1 ++ b._1, a._2 ++ b._2) }
      case Unapply.KApply(`unit`, List()) =>
        (List(), List())
//      case Unapply.KApply(`rwLabel`, List(left: K, right: K)) =>
//        val (xs: List[K], List()) = flatten(left, op, unit)
//        (xs, List(right))
      case Unapply.KRewrite(left: K, right: K) =>
        val (xs: List[K], List()) = flatten(left, op, unit)
        (xs, List(right))
      case _ => (List(k), List())
    }
  }

  def anonymousVariable(s: Sort): K = SortedADT.SortedKVariable("THE_VARIABLE", Att().add("sort", s.name))

}
