package org.kframework.parser

import org.kframework._
import org.kframework.kore._
import outer._
import collection.JavaConverters._

object TreeNodesToKORE {
  def apply(t: Term): K = t match {
    // TODO(Radu): the content of the constant should not be trimmed (see below) but we do this now due to an
    // but related to whitespace in the parser.
    case Constant(s, p, l) => KToken(p.sort, s.trim, locationToAtt(l.get()))
    case TermCons(items, p, l) => KApply(p.klabel.get, kore.KList(items.asScala map apply), locationToAtt(l.get()))
  }

  def locationToAtt(l: org.kframework.parser.Location): Attributes =
    Attributes(tiny.builtin.Location.apply(l.startLine, l.startColumn, l.endLine, l.endColumn))
}
