// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.outer

import org.kframework.kore._

case class Configuration(
  body: K,
  ensures: K,
  att: Attributes = Attributes()) extends Sentence {

  override def toString = "configuration " + xmlify(body) + " ensures " + ensures

  def xmlify(x: K): String = x match {
    case KApply(label, klist, att) => "<" + label.name + att.att.map(xmlifyAttributes).mkString(" ") + ">" +
      klist.map(xmlify).mkString(" ") + "<" + label.name + ">"
    case e => e.toString 
  }

  def xmlifyAttributes(x: K): String = x match {
    case KApply(label, klist, att) => label.name +
      (if (!klist.isEmpty)
        "=" + klist.map("\"" + _ + "\"").mkString(" ")
      else
        "")
  }
}

case class Bubble(ty: String, contents: String, att: Attributes = Attributes()) extends Sentence
