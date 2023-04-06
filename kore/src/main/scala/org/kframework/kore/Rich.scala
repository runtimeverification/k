// Copyright (c) K Team. All Rights Reserved.
package org.kframework.kore

import org.kframework.attributes.Att
import org.kframework.definition.Module
import collection.JavaConverters._

case class Rich(theModule: Module) {

  private val module = theModule

  implicit class RichKApply(k: KApply) {
  }

  implicit class RichKLabel(klabel: KLabel) {
    def productions = module.productionsFor(klabel)
  }

}
