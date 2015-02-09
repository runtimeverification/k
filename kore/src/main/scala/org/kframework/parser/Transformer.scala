// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.parser

import collection.JavaConverters._
import collection.mutable

abstract class Transformer[O] {
  // we expect this data structures to represent a DAG, so we
  // use a cache to remember nodes that we already visited.
  val cache = mutable.Map[Term, Either[O, Term]]()

  def apply(t: Term): Either[O, Term] =
    cache.getOrElseUpdate(t,
      t match {
        case a: Ambiguity => apply(a)
        case tc: TermCons => apply(tc)
        case kl: KList => apply(kl)
        case c: Constant => apply(c)
      })

  def apply(a: Ambiguity): Either[O, Term] = mapChildren(a)
  def apply(tc: TermCons): Either[O, Term] = mapChildrenStrict(tc)
  def apply(kl: KList): Either[O, Term] = mapChildren(kl)
  def apply(kl: Constant): Either[O, Term] = { Right(kl) }

  /**
   * Merges the set of problematic (i.e., Left) results.
   */
  def merge(a: O, b: O): O

  /**
   *  Transforms all children of the current item. If any of them is problematic,
   *  it merge(...)es all problems and returns Left(...).
   */
  protected def mapChildrenStrict(t: HasChildren): Either[O, Term] = {
    val newItems = t.items.asScala.map(apply)
    if (newItems.exists { t => t.isLeft })
      Left(newItems map { either => either.left.get } reduceLeft merge)
    else
      Right(t.replaceChildren(newItems.map(_.right.get).asJavaCollection));
  }

  /**
   * Transforms all children of the current item:
   *  - if all children are problematic (i.e., Left(...)), then return the
   * merge(...) of all problems.
   *  - if one child is left, return that child.
   *  - otherwise, i.e., a few of the children are correct, disregard all problems and
   * replace the children of the current element with the correct transformed children.
   */
  protected def mapChildren(t: HasChildren) = {
    val newItems = t.items.asScala.map(apply)
    val newCorrectItems = newItems.collect { case Right(v) => v }.toList
    newCorrectItems match {
      case List() if !newItems.isEmpty => {
        val allProblems = newItems.collect { case Left(v) => v }
        Left(allProblems reduceLeft merge)
      }
      case List(x) => Right(x)
      case l => Right(t.replaceChildren(newCorrectItems.asJavaCollection))
    }
  }
}
