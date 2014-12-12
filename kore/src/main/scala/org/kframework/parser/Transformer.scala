// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.parser

import collection.JavaConverters._

abstract class Transformer[O] {
  def apply(t: Term): Either[O, Term] = t match {
    case a: Ambiguity => apply(a)
    case tc: TermCons => apply(tc)
    case kl: KList => apply(kl)
    case c: Constant => apply(c)
  }

  def apply(a: Ambiguity): Either[O, Term] = mapChildren(a)
  def apply(tc: TermCons): Either[O, Term] = mapChildrenStrict(tc)
  def apply(kl: KList): Either[O, Term] = mapChildren(kl)
  def apply(kl: Constant): Either[O, Term] = { Right(kl) }

  def merge(a: O, b: O): O

  protected def mapChildrenStrict(t: HasChildren): Either[O, Term] = {
    val newItems = t.items.asScala.map(apply)
    if (newItems.exists { t => t.isLeft })
      Left(newItems map { _.left } reduceLeft { merge(_, _) })
    else
      Right(t.shallowCopy(newItems.map(_.right).asJavaCollection));
  }

  protected def mapChildren(t: HasChildren) = {
    val newItems = t.items.asScala
      .map(apply).collect { case Left(v) => v }
      .asJavaCollection
    Right(t.shallowCopy(newItems))
  }
}
