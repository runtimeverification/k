package org.kframework.kore

import Unapply._
import org.apache.commons.lang3.StringEscapeUtils

object Unparse {
  def apply(k: K) = k match {
    case KToken(sort, s) => "#token(" + sort + ",\"" + StringEscapeUtils.escapeJava(s) + "\")"
    case KApply(klabel, list) => klabel.toString + "(" + list.mkString(",") + ")"
    case KSequence(l) => if (l.isEmpty) ".K" else l.mkString("~>")
    case KRewrite(left, right) => left + "=>" + right
    case KVariable(name) => name
  }
}
