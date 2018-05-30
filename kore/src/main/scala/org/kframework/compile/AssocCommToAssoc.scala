package org.kframework.compile

import org.kframework.Collections._
import org.kframework.attributes.Att
import org.kframework.definition.{Module, Rule, Sentence}
import org.kframework.kore.SortedADT.SortedKVariable
import org.kframework.kore.KORE.{KApply, KRewrite}
import org.kframework.kore._

import collection.JavaConverters._
import scala.collection.Set

/**
  * Compiler pass for merging the rules as expected by FastRuleMatcher
  */
class AssocCommToAssoc extends Function[Module, Module] {

  override def apply(m: Module) = {
    Module(m.name, m.imports, m.localSentences flatMap {apply(_)(m)}, m.att)
  }

  private def apply(s: Sentence)(implicit m: Module): List[Sentence] = s match {
    //TODO(AndreiS): handle AC in requires and ensures
    case r: Rule if !r.att.contains("pattern-folding") =>
      val newBodies = apply(r.body)
      val substitutionOfVariables: Map[KVariable, K] = new FoldK[Map[KVariable, K]]() {
        type E = Map[KVariable, K]
        val unit: E = Map()

        def merge(a: E, b: E) = a ++ b

        override def apply(k: KRewrite): E = apply(k.left)
        override def apply(k: KApply) =
          merge(if(isAssocComm(k.klabel))
            computeSubstitution(k.klabel, k.items.asScala.toList)
          else
            unit, super.apply(k))
      }.apply(r.body)
      val substitute = new TransformK() {
        override def apply(v: KVariable) = substitutionOfVariables.getOrElse(v, v)
      }
      newBodies
        .map(substitute)
        .map {Rule(_, r.requires, r.ensures, r.att)}

//      if(substitutionOfVariables.nonEmpty) {
//        println(newBodies)
//        println(substitutionOfVariables)
//      }
    case _ => List(s)
  }

  private def apply(k: K)(implicit m: Module): List[K] = k match {
    case Unapply.KApply(label: KLabel, children: List[K]) if isAssocComm(label) =>
      convert(label, children)
    case Unapply.KApply(label: KLabel, children: List[K]) =>
      crossProduct(children map apply) map {KApply(label,(_: _*))}
    case Unapply.KRewrite(left: K, right: K) =>
      apply(left) map {KRewrite(_, right, Att.empty)}
    case _ =>
      List(k)
  }

  private def isAssocComm(label: KLabel)(implicit m: Module): Boolean = {
    val att: Att = m.attributesFor.getOrElse(label, Att.empty)
    att.contains(Att.assoc) && att.contains(Att.comm)
  }

  private def convert(label: KLabel, children: List[K])(implicit m: Module): List[K] = {
    val opSort: Sort = m.signatureFor(label).head._2

    val (elements: Seq[K], nonElements: Seq[K]) = children partition {
      case v: SortedKVariable => m.subsorts.lessThan(v.sort, opSort);
      case _ => true
    }

    assert(nonElements.size <= 1)
    assert(nonElements.headOption forall { case v: KVariable => v.name.equals("THE_VARIABLE") || v.name.startsWith("DotVar") || v.att.contains("anonymous") })
    val frameOption = nonElements.headOption

    val convertedChildren: List[List[K]] = frameOption match {
      case Some(v: KVariable) if v.name.equals("THE_VARIABLE") =>
        elements.permutations.toList map {
          _.foldRight(List(anonymousVariable(opSort))) { (e, l) => anonymousVariable(opSort) :: e :: l }
        }
      //TODO(AndreiS): check the variable is free (not constrained elsewhere by the rule)
      case Some(v: KVariable) if v.name.startsWith("DotVar") || v.att.contains("anonymous") =>
        elements.permutations.toList map {
          _.foldRight(List(dotVariable(opSort, 0))) { (e, l) => dotVariable(opSort, (l.size + 1) / 2) :: e :: l }
        }
      case None =>
        elements.toList.permutations.toList
    }

    convertedChildren flatMap { cs => crossProduct(cs map apply) } map {KApply(label,(_: _*))}
  }

  private def computeSubstitution(label: KLabel, children: List[K])(implicit m: Module): Map[KVariable, K] = {
    val opSort: Sort = m.signatureFor(label).head._2

    val (elements: Seq[K], nonElements: Seq[K]) = children partition {
      case v: SortedKVariable => m.subsorts.lessThan(v.sort, opSort);
      case _ => true
    }

    assert(nonElements.size <= 1)
    assert(nonElements.headOption forall { case v: KVariable => v.name.equals("THE_VARIABLE") || v.name.startsWith("DotVar") || v.att.contains("anonymous") })
    val frameOption = nonElements.headOption

    frameOption match {
      case Some(v: KVariable) if v.name.startsWith("DotVar") || v.att.contains("anonymous") =>
        Map(v -> KApply(label,((0 to elements.size) map {dotVariable(opSort, _)}: _*)))
      case _ => Map()
    }
  }

  private def substituteFrame(k: K, name: String, substitute: K): K = k match {
    case Unapply.KApply(label: KLabel, children: List[K]) => KApply(label, children map {substituteFrame(_, name, substitute)}: _*)
    case Unapply.KVariable(`name`) => substitute
    case _: K => k
  }

  private def crossProduct[T](lls: List[List[T]]): List[List[T]] = {
    lls match {
      case (head: List[T]) :: (tail: List[List[T]]) =>
        for {x <- head; (xs: List[T]) <- crossProduct(tail)} yield x :: xs
      case List() => List(List())
    }
  }

  private def anonymousVariable(s: Sort): K = SortedADT.SortedKVariable("THE_VARIABLE", Att.empty.add(classOf[Sort], s))

  private def dotVariable(s: Sort, n: Int): K = SortedADT.SortedKVariable(s.toString + "_DotVar" + n, Att.empty.add(classOf[Sort], s))

}
