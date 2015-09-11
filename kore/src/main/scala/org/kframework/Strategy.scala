package org.kframework

import org.kframework.attributes.Att
import org.kframework.builtin.Labels
import org.kframework.definition.{DefinitionTransformer, ModuleTransformer, Rule}
import org.kframework.kore.KORE
import org.kframework.kore.Unapply.{KApply, KLabel}


object Strategy {

  val addStrategyCellToRulesTransformer =
    DefinitionTransformer(
      ModuleTransformer.fromSentenceTransformer({
        (module, r) =>
          val rich = kore.Rich(module)

          import rich._

          r match {
            case r: Rule if !r.body.contains({ case KApply(KLabel("<s>"), _) => true }) =>
              println("old: "+r.body)
              val newBody = r.body match {
                case KApply(klabel, _) if !module.attributesFor.contains(klabel) || klabel.att.contains(Att.Function) =>
                  // todo: "!module.attributesFor.contains(klabel) ||" when #1723 is fixed
                  KORE.KApply(KORE.KLabel(Labels.Cells), r.body)
                case _ => r.body
              }
              println("new: "+newBody)
              Rule(newBody, r.requires, r.ensures, r.att)
            case r => r
          }
      }, "add strategy cell to rules"))

}
