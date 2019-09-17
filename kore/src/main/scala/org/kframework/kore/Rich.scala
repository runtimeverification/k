package org.kframework.kore

import org.kframework.attributes.Att
import org.kframework.definition.Module
import collection.JavaConverters._

case class Rich(theModule: Module) {

  private val module = theModule

  implicit class RichKApply(k: KApply) {
    def att = k.klabel.att
  }

  implicit class RichKLabel(klabel: KLabel) {
    def productions = module.productionsFor(klabel)

    def att: Att = Att(productions.flatMap(_.att.att).toMap)
  }

}
