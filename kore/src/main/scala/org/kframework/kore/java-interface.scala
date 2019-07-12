package org.kframework.kore

import org.kframework.attributes.Att
import org.kframework.Collections


abstract class KRewrite_JavaWrapper(override val left : K, override val right : K) extends KRewrite {
  override def att : Att = Att.empty
}

abstract class KVariable_JavaWrapper(override val name : String) extends KVariable {
  override def att : Att = Att.empty
  override def params : Seq[Sort] = Collections.Seq()
}
