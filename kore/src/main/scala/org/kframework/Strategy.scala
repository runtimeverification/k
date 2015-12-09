package org.kframework

import org.kframework.attributes.Att
import org.kframework.builtin.KLabels
import org.kframework.definition.{DefinitionTransformer, ModuleTransformer, Rule}
import org.kframework.kore.KORE
import org.kframework.kore.Unapply.{KApply, KLabel}

object Strategy {
  val strategyCellName = "<s>"
  val strategyCellLabel = KORE.KLabel(strategyCellName)
}

class Strategy(heatCool: Boolean) {
  import Strategy._

  val addStrategyCellToRulesTransformer =
    DefinitionTransformer(
      ModuleTransformer.fromSentenceTransformer({
        (module, r) =>
          val rich = kore.Rich(module)

          import rich._
          
          if (!module.importedModules.exists(_.name == "STRATEGY")) {
            r
          } else
            r match {
              case r: Rule if !r.body.contains({ case k: kore.KApply => k.klabel.name.contains("<s>") }) =>
                val newBody = r.body match {
                  case KApply(klabel, _) if !module.attributesFor.contains(klabel) || !klabel.att.contains(Att.Function) =>
                    // todo: "!module.attributesFor.contains(klabel) ||" when #1723 is fixed

                    def makeRewrite(tag: String) =
                      KORE.KApply(KORE.KLabel(KLabels.KSEQ),
                        KORE.KRewrite(
                          KORE.KApply(KORE.KLabel("#applyRule"), KORE.KToken(tag, KORE.Sort("#RuleTag"))),
                          KORE.KApply(KORE.KLabel("#appliedRule"), KORE.KToken(tag, KORE.Sort("#RuleTag")))),
                        KORE.KVariable("SREST"))

                    val strategy =
                      if (r.att.contains("tag")) {
                        makeRewrite(r.att.get[String]("tag").get)
                      } else if (heatCool && r.att.contains(Att.heat)) {
                        makeRewrite("heat")
                      } else if (heatCool && r.att.contains(Att.cool)) {
                        makeRewrite("cool")
                      } else {
                        makeRewrite("regular")
                      }

                    KORE.KApply(KORE.KLabel(KLabels.CELLS), r.body,
                      KORE.KApply(strategyCellLabel,
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
