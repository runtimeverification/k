// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.definition

import org.kframework.kore._
import org.kframework.attributes._
import org.kframework.kore.{KORE => con}

case class Configuration(body: K, ensures: K, att: Att = Att()) extends Sentence with OuterKORE {

  //  override def toString = "configuration " + xmlify(body) + " ensures " + ensures

  //  def xmlify(x: K): String = x match {
  //    case KApply(label, klist, att) if att.contains("cell") => {
  //      val atts = att.att.filterNot(_ == Configuration.cellMarker)
  //
  //      val attsString = if (atts.size > 0)
  //        " " + atts.map(xmlifyAttributes).mkString(" ")
  //      else
  //        ""
  //
  //      "<" + label.name + attsString + ">" +
  //        klist.map(xmlify _).mkString(" ") +
  //        "</" + label.name + ">"
  //    }
  //    //    case KBag(klist) =>
  //    //      if (klist.isEmpty)
  //    //        ".Bag"
  //    //      else
  //    //        klist map { xmlify _ } mkString " "
  //    case e => e.toString
  //  }
  //
  //  def xmlifyAttributes(x: K): String = x match {
  //    case KApply(label, klist, att) => label.name +
  //      (if (!klist.isEmpty)
  //        "=" + klist.map({ e: K => "\"" + e + "\"" }).mkString(" ")
  //      else
  //        "")
  //  }
}

object Configuration {
  val cellMarker = con.KApply(con.KLabel("cell"), con.KList(), Att());
}

case class Bubble(sentenceType: String, contents: String, att: Att = Att()) extends Sentence
