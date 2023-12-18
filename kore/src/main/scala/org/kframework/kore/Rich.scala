// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kore

import collection.JavaConverters._
import org.kframework.attributes.Att
import org.kframework.definition.Module

case class Rich(theModule: Module) {

  private val module = theModule

  implicit class RichKApply(k: KApply) {}

  implicit class RichKLabel(klabel: KLabel) {
    def productions = module.productionsFor(klabel)
  }

}
