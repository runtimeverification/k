// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

package org.kframework.parser

import java.util
import org.kframework.Collections._
import scala.jdk.CollectionConverters._

class Ignore

object Ignore extends Ignore

abstract class ChildrenMapping[E, W] {

  def applyTerm(t: Term): (Either[E, Term], W)

  protected def simpleError(err: E): (Either[E, Term], W)        = (Left(err), warningUnit)
  protected def simpleResult(result: Term): (Either[E, Term], W) = (Right(result), warningUnit)

  /**
   * Transforms all children of the current item. If any of them is problematic, it merge(...)es all
   * problems and returns Left(...). If everything is ok, replace children, and merge all warnings.
   */
  def mapChildrenStrict(t: HasChildren): (Either[E, Term], W) = {
    val allResults = t.items.asScala.map(applyTerm) // visit all children
    val (eithers: Iterable[Either[E, Term]], warnings: Iterable[W]) = allResults.unzip
    val mergedWarnings = warnings.foldLeft(warningUnit)(mergeWarnings)

    if (eithers.exists(t => t.isLeft)) {
      val mergedErrors = eithers.collect { case Left(err) => err }.foldLeft(errorUnit)(mergeErrors)
      (Left(mergedErrors), mergedWarnings)
    } else {
      val newChildren: Iterable[Term] = eithers.map(_.toOption.get)
      (Right(t.replaceChildren(newChildren.asJavaCollection)), mergedWarnings)
    }
  }

  /**
   * Transforms all children of the current item:
   *   - if all children are problematic (i.e., Left(...)), then return the merge(...) of all
   *     problems.
   *   - if one child is left, return that child.
   *   - otherwise, i.e., a few of the children are correct, disregard all problems and replace the
   *     children of the current element with the correct transformed children.
   */
  def mapChildren(t: HasChildren): (Either[E, Term], W) = {
    val allResults1 = t.items.asScala.map(applyTerm) // visit all children
    val allResults = allResults1.flatMap {
      case (Right(Ambiguity(items)), warns) =>
        immutable(items).map(t => (Right(t): Either[E, Term], warns))
      case x => Set(x)
    }

    val (eithers: Iterable[Either[E, Term]], warnings: Iterable[W]) = allResults.unzip
    val newCorrectItems: List[(Term, W)] = allResults.collect { case (Right(v), w) =>
      (v, w)
    }.toList
    newCorrectItems match {
      case List() =>
        val mergedWarnings = warnings.foldLeft(warningUnit)(mergeWarnings)
        val mergedErrors =
          eithers.collect { case Left(err) => err }.foldLeft(errorUnit)(mergeErrors)
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
 * Visitor pattern for the front end classes. Applies the visitor transformation on each node, and
 * returns a tuple of either a term, or a set of errors, and a set of possible warnings.
 * @tparam E
 *   container for errors.
 * @tparam W
 *   container for warnings.
 */
abstract class GeneralTransformer[E, W] extends ChildrenMapping[E, W] {
  // we expect this data structures to represent a DAG, so we
  // use a cache to remember nodes that we already visited.
  val cache = new util.IdentityHashMap[Term, (Either[E, Term], W)]()

  def applyTerm(t: Term): (Either[E, Term], W) = apply(t)

  def apply(t: Term): (Either[E, Term], W) = {
    if (cache.containsKey(t)) {
      return cache.get(t)
    }
    val res =
      t match {
        case a: Ambiguity           => apply(a)
        case p: ProductionReference => apply(p)
      }
    cache.put(t, res)
    res
  }

  def apply(p: ProductionReference): (Either[E, Term], W) = p match {
    case tc: TermCons => apply(tc)
    case c: Constant  => apply(c)
  }

  def apply(a: Ambiguity): (Either[E, Term], W) = mapChildren(a)
  def apply(tc: TermCons): (Either[E, Term], W) = mapChildrenStrict(tc)
  def apply(c: Constant): (Either[E, Term], W)  = simpleResult(c)
}

abstract class SetsGeneralTransformer[E, W]
    extends GeneralTransformer[java.util.Set[E], java.util.Set[W]] {

  /**
   * Merges the set of problematic (i.e., Left) results.
   */
  def mergeErrors(a: java.util.Set[E], b: java.util.Set[E]): java.util.Set[E] = {
    val c = new java.util.HashSet[E](a)
    c.addAll(b)
    c
  }

  val errorUnit: java.util.Set[E] = new java.util.HashSet[E]()

  val warningUnit: java.util.Set[W] = new java.util.HashSet[W]()

  /**
   * Merges the set of problematic (i.e., Left) results.
   */
  def mergeWarnings(a: java.util.Set[W], b: java.util.Set[W]): java.util.Set[W] = {
    val c = new java.util.HashSet[W](a)
    c.addAll(b)
    c
  }
}

/**
 * Visitor pattern for the front end classes. Applies the visitor transformation on each node, and
 * returns either a term, or a set of errors. (no warnings)
 * @tparam E
 *   container for errors.
 */
abstract class TransformerWithErrors[E] extends ChildrenMapping[E, Ignore] {

  def applyTerm(t: Term): (Either[E, Term], Ignore) = (apply(t), Ignore)
  // we expect this data structures to represent a DAG, so we
  // use a cache to remember nodes that we already visited.
  val cache = new util.IdentityHashMap[Term, Either[E, Term]]

  def apply(t: Term): Either[E, Term] = {
    if (cache.containsKey(t)) {
      return cache.get(t)
    }
    val res =
      t match {
        case a: Ambiguity           => apply(a)
        case p: ProductionReference => apply(p)
      }
    cache.put(t, res)
    res
  }

  def apply(p: ProductionReference): Either[E, Term] = p match {
    case tc: TermCons => apply(tc)
    case c: Constant  => apply(c)
  }

  def apply(a: Ambiguity): Either[E, Term] = mapChildren(a)._1
  def apply(tc: TermCons): Either[E, Term] = mapChildrenStrict(tc)._1
  def apply(c: Constant): Either[E, Term]  = Right(c)

  override def mergeWarnings(a: Ignore, b: Ignore): Ignore = Ignore
  override val warningUnit: Ignore                         = Ignore
}

abstract class SetsTransformerWithErrors[E] extends TransformerWithErrors[java.util.Set[E]] {

  /**
   * Merges the set of problematic (i.e., Left) results.
   */
  def mergeErrors(a: java.util.Set[E], b: java.util.Set[E]): java.util.Set[E] = {
    val c = new java.util.HashSet[E](a)
    c.addAll(b)
    c
  }

  val errorUnit: java.util.Set[E] = new java.util.HashSet[E]()
}

/**
 * Visitor pattern for the front end classes. Applies the visitor transformation on each node, and
 * returns a term. (no errors and no warnings)
 */
abstract class SafeTransformer extends ChildrenMapping[Ignore, Ignore] {

  def applyTerm(t: Term): (Either[Ignore, Term], Ignore) = (Right(apply(t)), Ignore)
  // we expect this data structures to represent a DAG, so we
  // use a cache to remember nodes that we already visited.
  val cache = new util.IdentityHashMap[Term, Term]

  def apply(t: Term): Term = {
    if (cache.containsKey(t)) {
      return cache.get(t)
    }
    val res =
      t match {
        case a: Ambiguity           => apply(a)
        case p: ProductionReference => apply(p)
      }
    cache.put(t, res)
    res
  }

  def apply(p: ProductionReference): Term = p match {
    case tc: TermCons => apply(tc)
    case c: Constant  => apply(c)
  }

  def apply(a: Ambiguity): Term = mapChildren(a)._1.toOption.get
  def apply(tc: TermCons): Term = mapChildrenStrict(tc)._1.toOption.get
  def apply(c: Constant): Term  = c

  def mergeWarnings(a: Ignore, b: Ignore): Ignore = Ignore
  val warningUnit: Ignore                         = Ignore
  def mergeErrors(a: Ignore, b: Ignore): Ignore   = Ignore
  val errorUnit: Ignore                           = Ignore
}
