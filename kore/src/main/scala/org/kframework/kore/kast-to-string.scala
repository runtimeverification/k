// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

trait KApplyToString {
  self: KApply =>
  override def toString() = klabel.toString + "(" + contents.mkString(",") + ")"
}

trait AttributesToString {
  self: Attributes =>

  override def toString() = "[" +
    (att map {
      case KApply(KLabel(keyName), KList(KToken(_, KString(value), _)), _) => keyName + "(" + value + ")"
      // FIXME: This is to prevent printing metadata saved as attributes. Currently this metadata
      // is used to guide translating KORE back to KIL.
      case a => a.toString
    }).toList.sorted.mkString(" ") +
    "]" // TODO: remove brackets if nothing is printed inside

  def postfixString = if (att.isEmpty) "" else (" " + toString())
}

trait SortToString {
  self: Sort =>
  override def toString = name
}

trait KTokenToString {
  self: KToken =>
  override def toString = s.s
}

trait KLabelToString {
  self: KLabel =>
  override def toString = name
}

trait KRewriteToString {
  self: KRewrite =>
  override def toString = left.toString + "=>" + right.toString
}

trait KSequenceToString {
  self: KSequence =>
  override def toString =
    if(isEmpty) ".K" else mkString("~>")
}

trait KStringToString {
  self: KString =>
  override def toString = s
}
