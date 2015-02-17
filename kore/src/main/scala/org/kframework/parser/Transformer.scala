// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.parser

import collection.JavaConverters._
import collection.mutable


abstract class GeneralTransfomer[E, W] {

  // we expect this data structures to represent a DAG, so we
  // use a cache to remember nodes that we already visited.
  val cache = mutable.Map[Term, (Either[E, Term], W)]()

  def apply(t: Term): (Either[E, Term], W) =
    cache.getOrElseUpdate(t,
      t match {
        case a: Ambiguity => apply(a)
        case kl: KList => apply(kl)
        case p: ProductionReference => apply(p)
      })

  def apply(p: ProductionReference): (Either[E, Term], W) = p match {
    case tc: TermCons => apply(tc)
    case c: Constant => apply(c)
  }

  def apply(a: Ambiguity): (Either[E, Term], W) = mapChildren(a)
  def apply(tc: TermCons): (Either[E, Term], W) = mapChildrenStrict(tc)
  def apply(kl: KList): (Either[E, Term], W) = mapChildrenStrict(kl)
  def apply(c: Constant): (Either[E, Term], W) = { (Right(c), warningUnit) }

  /**
   * Merges the set of problematic (i.e., Left) results.
   */
  def mergeErrors(a: E, b: E): E

  val warningUnit: W

  val errorUnit: E
  /**
   * Merges the set of problematic (i.e., Left) results.
   */
  def mergeWarnings(a: W, b: W): W

  /**
   * Transforms all children of the current item. If any of them is problematic,
   * it merge(...)es all problems and returns Left(...).
   * If everything is ok, replace children, and merge all warnings.
   */
  protected def mapChildrenStrict(t: HasChildren): (Either[E, Term], W) = {
    val allResults = t.items.asScala.map(apply) // visit all children
    val (eithers: Iterable[Either[E, Term]], warnings: Iterable[W]) = allResults.unzip
    val mergedWarnings = warnings.foldLeft(warningUnit)(mergeWarnings)

    if (eithers.exists { t => t.isLeft }) {
      val mergedErrors = (eithers collect { case Left(err) => err }).foldLeft(errorUnit)(mergeErrors)
      (Left(mergedErrors), mergedWarnings)
    } else {
      val newChildren: Iterable[Term] = eithers map { _.right.get }
      (Right(t.replaceChildren(newChildren.asJavaCollection)), mergedWarnings)
    }
  }

  /**
   * Transforms all children of the current item:
   * - if all children are problematic (i.e., Left(...)), then return the
   * merge(...) of all problems.
   * - if one child is left, return that child.
   * - otherwise, i.e., a few of the children are correct, disregard all problems and
   * replace the children of the current element with the correct transformed children.
   */
  protected def mapChildren(t: HasChildren): (Either[E, Term], W) = {
    val allResults = t.items.asScala.map(apply) // visit all children
    val (eithers: Iterable[Either[E, Term]], warnings: Iterable[W]) = allResults.unzip
    val newCorrectItems: List[(Term, W)] = allResults.collect { case (Right(v), w) => (v, w) }.toList
    newCorrectItems match {
      case List() => {
        val mergedWarnings = warnings.foldLeft(warningUnit)(mergeWarnings)
        val mergedErrors = (eithers collect { case Left(err) => err }).foldLeft(errorUnit)(mergeErrors)
        (Left(mergedErrors), mergedWarnings)
      }
      case List((term, w)) => (Right(term), w)
      case l =>
        val (newTerms, warnings) = l.unzip
        (Right(t.replaceChildren(newTerms.asJava)), warnings.foldLeft(warningUnit)(mergeWarnings))
    }
  }
}

abstract class TransformerWithErrors[E] {

  val outerThis = this

  private[this] val generalTransformer = new GeneralTransfomer[E, Unit] {
    def mergeErrors(a: E, b: E): E = outerThis.merge(a, b)
    val errorUnit: E = outerThis.errorUnit

    def mergeWarnings(a: Unit, b: Unit): Unit = Unit
    val warningUnit: Unit = Unit
  }

  def apply(t: Term): Either[E, Term] = generalTransformer.apply(t)._1

  def apply(p: ProductionReference): Either[E, Term] = generalTransformer.apply(p)._1
  def apply(a: Ambiguity): Either[E, Term] = generalTransformer.apply(a)._1
  def apply(tc: TermCons): Either[E, Term] = generalTransformer.apply(tc)._1
  def apply(kl: KList): Either[E, Term] = generalTransformer.apply(kl)._1
  def apply(c: Constant): Either[E, Term] = generalTransformer.apply(c)._1

  /**
   * Merges the set of problematic (i.e., Left) results.
   */
  def merge(a: E, b: E): E

  val errorUnit: E
}

abstract class SafeTransformer {

  val outerThis = this

  private[this] val generalTransformer = new TransformerWithErrors[Unit] {
    def merge(a: Unit, b: Unit): Unit = Unit
    val errorUnit: Unit = Unit
  }

  def apply(t: Term): Term = generalTransformer.apply(t).right.get

  def apply(p: ProductionReference): Term = generalTransformer.apply(p).right.get
  def apply(a: Ambiguity): Term = generalTransformer.apply(a).right.get
  def apply(tc: TermCons): Term = generalTransformer.apply(tc).right.get
  def apply(kl: KList): Term = generalTransformer.apply(kl).right.get
  def apply(c: Constant): Term = generalTransformer.apply(c).right.get
}
