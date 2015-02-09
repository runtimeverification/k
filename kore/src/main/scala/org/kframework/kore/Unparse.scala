package org.kframework.kore

import Unapply._
import org.apache.commons.lang3.StringEscapeUtils

object Unparse extends {
  def apply(k: K): String = k match {
    case KToken(sort, s) => "#token(" + sort + ",\"" + StringEscapeUtils.escapeJava(s) + "\")"
    case KSequence(l) => if (l.isEmpty) ".K" else l.map(apply).mkString("~>")
    case KRewrite(left, right) => apply(left) + "=>" + apply(right)
    case KApply(klabel, list) => klabel.name + "(" + list.map(apply).mkString(",") + ")"
    case KVariable(name) => name
  }
}
