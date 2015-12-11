package org.kframework.kore

import org.kframework.attributes.Att
import org.kframework.definition.Module
import collection.JavaConverters._

case class Rich(theModule: Module) {

  private val module = theModule

  implicit class RichK(k: K) {
    def contains(f: PartialFunction[K, Boolean]) = find(f) != None

    def find(f: PartialFunction[K, Boolean]): Option[K] = {
      val ff = f.orElse[K, Boolean]({ case k => false })
      if (ff(k))
        Some(k)
      else
        (k match {
          case k: KCollection => k.items.asScala.find(ff)
          case _ => None
        })
    }
  }

  implicit class RichKApply(k: KApply) {
    def att = k.klabel.att
  }

  implicit class RichKLabel(klabel: KLabel) {
    def productions = module.productionsFor(klabel)

    def att: Att = Att(productions.flatMap(_.att.att))
  }

}
