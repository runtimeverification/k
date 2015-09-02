package org.kframework.compile

import org.kframework.definition.Module

class LabelInfoFromModule(module: Module) extends LabelInfo {
  module.productionsFor.foreach({
    case (label, prods) =>
      def att(key : String) = prods.exists(_.att.contains(key))
      addLabel(prods.head.sort.toString, label.toString, att("assoc"), att("comm"), att("function"))
  })
}