// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile

import org.kframework.attributes.Att
import org.kframework.definition.Module

class LabelInfoFromModule(module: Module) extends LabelInfo {
  module.productionsFor.foreach { case (label, prods) =>
    def att(key: Att.Key) = prods.exists(_.att.contains(key))
    addLabel(
      prods.head.sort,
      label.toString,
      att(Att.ASSOC),
      att(Att.COMM),
      att(Att.FUNCTION),
      prods.head
    )
  }
}
