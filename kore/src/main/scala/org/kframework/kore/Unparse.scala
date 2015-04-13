package org.kframework.kore

import Unapply._
import org.apache.commons.lang3.StringEscapeUtils
import collection.JavaConverters._

/**
 * Pretty prints inner KORE structures to labeled form.
 */

object Unparse extends {
  def apply(k: K): String = k match {
    case KToken(sort, s) => "#token(" + sort + ",\"" + StringEscapeUtils.escapeJava(s) + "\")"
    // TODO: Radu: fix string escaping above; see issue #1359
    case KSequence(l) =>
      if (l.isEmpty)
        ".K"
      else
        "~>(" + l.map(apply).mkString(",") + ")"
    //        l.map("(" + apply(_) + ")").mkString("~>")
    case KRewrite(left, right) => "=>(" + apply(left) + "," + apply(right) + ")"
    // apply(left) + "=>" + apply(right)
    case kapp: KApply => kapp.klabel.name + "(" + kapp.klist.items.asScala.map(apply).mkString(",") + ")"
    case KVariable(name) => name
  }
}
