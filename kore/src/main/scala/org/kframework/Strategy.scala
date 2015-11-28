package org.kframework

import org.kframework.attributes.Att
import org.kframework.builtin.KLabels
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

          // hackish test for whether we're using strategies or not
          // TODO: replace with something more principled
          if (!module.importedModules.exists(_.name == "STRATEGY")) {
            r
          } else
            r match {
              case r: Rule if !r.body.contains({ case KApply(KLabel("<s>"), _) => true }) =>
                val newBody = r.body match {
                  case KApply(klabel, _) if !module.attributesFor.contains(klabel) || klabel.att.contains(Att.Function) =>
                    // todo: "!module.attributesFor.contains(klabel) ||" when #1723 is fixed
                    val strategy =
                      if (r.att.contains(Att.heat))
                        KORE.KApply(KORE.KLabel("heat"))
                      else if (r.att.contains(Att.cool))
                        KORE.KApply(KORE.KLabel("cool"))
                      else
                        KORE.KRewrite(KORE.KApply(KORE.KLabel("regular")), KORE.KApply(KORE.KLabel("cool")))

                    KORE.KApply(KORE.KLabel(KLabels.CELLS), r.body,
                      KORE.KApply(KORE.KLabel("<s>"),
                        KORE.KApply(KORE.KLabel(KLabels.NO_DOTS)),
                        strategy,
                        KORE.KApply(KORE.KLabel(KLabels.NO_DOTS))
                      ))
                  case _ => r.body
                }
                Rule(newBody, r.requires, r.ensures, r.att)
              case r => r
            }
      }, "add strategy cell to rules"))

}
