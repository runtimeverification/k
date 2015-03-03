// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.parser

import com.google.common.collect.Sets

import collection.JavaConverters._
import org.kframework.Collections._


class Ignore

object Ignore extends Ignore

trait ChildrenMapping[E, W] {

  def applyTerm(t: Term): (Either[E, Term], W)

  /**
   * Transforms all children of the current item. If any of them is problematic,
   * it merge(...)es all problems and returns Left(...).
   * If everything is ok, replace children, and merge all warnings.
   */
  def mapChildrenStrict(t: HasChildren): (Either[E, Term], W) = {
    val allResults = t.items.asScala.map(applyTerm) // visit all children
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
  def mapChildren(t: HasChildren): (Either[E, Term], W) = {
    val allResults1 = t.items.asScala.map(applyTerm) // visit all children
    val allResults = allResults1 flatMap {
        case (Right(Ambiguity(items, _)), warns) => immutable(items) map { t => (Right(t): Either[E, Term], warns) }
        case x => Set(x)
      }

    val (eithers: Iterable[Either[E, Term]], warnings: Iterable[W]) = allResults.unzip
    val newCorrectItems: List[(Term, W)] = allResults.collect { case (Right(v), w) => (v, w) }.toList
    newCorrectItems match {
      case List() =>
        val mergedWarnings = warnings.foldLeft(warningUnit)(mergeWarnings)
        val mergedErrors = (eithers collect { case Left(err) => err }).foldLeft(errorUnit)(mergeErrors)
        (Left(mergedErrors), mergedWarnings)
      case List((term, w)) => (Right(term), w)
      case l =>
        val (newTerms, warnings) = l.unzip
        (Right(t.replaceChildren(newTerms.asJava)), warnings.foldLeft(warningUnit)(mergeWarnings))
    }
  }

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
}

/**
 * Visitor pattern for the front end classes.
 * Applies the visitor transformation on each node, and returns a tuple of either a term, or a set of errors, and
 * a set of possible warnings.
 * @tparam E container for errors.
 * @tparam W container for warnings.
 */
abstract class GeneralTransformer[E, W] extends ChildrenMapping[E, W] {

  import collection.mutable
  // we expect this data structures to represent a DAG, so we
  // use a cache to remember nodes that we already visited.
  val cache = mutable.Map[Term, (Either[E, Term], W)]()

  def applyTerm(t: Term): (Either[E, Term], W) = apply(t)

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
}

trait EAsSet[E] {
  /**
   * Merges the set of problematic (i.e., Left) results.
   */
  def mergeErrors(a: java.util.Set[E], b: java.util.Set[E]): java.util.Set[E] = Sets.union(a, b)

  val errorUnit: java.util.Set[E] = makeErrorSet()

  @annotation.varargs def makeErrorSet(l:E*) = l.toSet.asJava
}

trait WAsSet[W] {
  val warningUnit: java.util.Set[W] = makeWarningSet()
  /**
   * Merges the set of problematic (i.e., Left) results.
   */
  def mergeWarnings(a: java.util.Set[W], b: java.util.Set[W]): java.util.Set[W] = Sets.union(a, b)

  @annotation.varargs def makeWarningSet(l:W*) = l.toSet.asJava
}

abstract class SetsGeneralTransformer[E, W]
  extends GeneralTransformer[java.util.Set[E], java.util.Set[W]] with EAsSet[E] with WAsSet[W]

/**
 * Visitor pattern for the front end classes.
 * Applies the visitor transformation on each node, and returns either a term, or a set of errors. (no warnings)
 * @tparam E container for errors.
 */
abstract class TransformerWithErrors[E] extends ChildrenMapping[E, Ignore] {

  def applyTerm(t: Term): (Either[E, Term], Ignore) = (apply(t), Ignore)

  import collection.mutable
  // we expect this data structures to represent a DAG, so we
  // use a cache to remember nodes that we already visited.
  val cache = mutable.Map[Term, Either[E, Term]]()

  def apply(t: Term): Either[E, Term] =
    cache.getOrElseUpdate(t,
      t match {
        case a: Ambiguity => apply(a)
        case kl: KList => apply(kl)
        case p: ProductionReference => apply(p)
      })

  def apply(p: ProductionReference): Either[E, Term] = p match {
    case tc: TermCons => apply(tc)
    case c: Constant => apply(c)
  }

  def apply(a: Ambiguity): Either[E, Term] = mapChildren(a)._1
  def apply(tc: TermCons): Either[E, Term] = mapChildrenStrict(tc)._1
  def apply(kl: KList): Either[E, Term] = mapChildrenStrict(kl)._1
  def apply(c: Constant): Either[E, Term] = Right(c)

  override def mergeWarnings(a: Ignore, b: Ignore) = Ignore
  override val warningUnit = Ignore
}

abstract class SetsTransformerWithErrors[E]
  extends TransformerWithErrors[java.util.Set[E]] with EAsSet[E]

/**
 * Visitor pattern for the front end classes.
 * Applies the visitor transformation on each node, and returns a term. (no errors and no warnings)
 */
abstract class SafeTransformer extends ChildrenMapping[Ignore, Ignore] {

  def applyTerm(t: Term): (Either[Ignore, Term], Ignore) = (Right(apply(t)), Ignore)

  import collection.mutable
  // we expect this data structures to represent a DAG, so we
  // use a cache to remember nodes that we already visited.
  val cache = mutable.Map[Term, Term]()

  def apply(t: Term): Term =
    cache.getOrElseUpdate(t,
      t match {
        case a: Ambiguity => apply(a)
        case kl: KList => apply(kl)
        case p: ProductionReference => apply(p)
      })

  def apply(p: ProductionReference): Term = p match {
    case tc: TermCons => apply(tc)
    case c: Constant => apply(c)
  }

  def apply(a: Ambiguity): Term = mapChildren(a)._1.right.get
  def apply(tc: TermCons): Term = mapChildrenStrict(tc)._1.right.get
  def apply(kl: KList): Term = mapChildrenStrict(kl)._1.right.get
  def apply(c: Constant): Term = c

  def mergeWarnings(a: Ignore, b: Ignore) = Ignore
  val warningUnit = Ignore
  def mergeErrors(a: Ignore, b: Ignore) = Ignore
  val errorUnit = Ignore
}
