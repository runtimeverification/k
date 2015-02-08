package org.kframework

import org.kframework.attributes.Att

package object tiny {
  type Sort = kore.Sort

  lazy val True = new And(Set(), Att())
  lazy val False = new Or(Set(), Att())
}
