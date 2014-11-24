// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore

trait KApplyToString {
  self: KApply =>
  override def toString() = klabel.toString + "(" + mkString(",") + ")" + att.postfixString
}

trait SortToString {
  self: Sort =>
  override def toString = name
}

trait KTokenToString {
  self: KToken =>
  override def toString = s.s
}

trait KVariableToString {
  self: KVariable =>
  override def toString = name + att.postfixString
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
    if (isEmpty) ".K" else mkString("~>")
}

trait KStringToString {
  self: KString =>
  override def toString = s
}

trait KListToString {
  self: KList =>
  override def toString = "KList(" + this.mkString(",") + ")"
}
