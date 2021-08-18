package org.kframework

import org.kframework.attributes.Att
import org.kframework.builtin.BooleanUtils
import org.kframework.builtin.KLabels
import org.kframework.builtin.Sorts
import org.kframework.compile.RewriteToTop
import org.kframework.definition.{DefinitionTransformer, ModuleTransformer, Module, Rule, Definition}
import org.kframework.kore.ExistsK
import org.kframework.kore.KApply
import org.kframework.kore.KORE
import org.kframework.kore.Sort
import org.kframework.kore.Unapply.{KApply, KLabel}

object Strategy {
  val strategyCellName = "<s>"
  val strategyCellLabel = KORE.KLabel(strategyCellName)

  def addStrategyRuleToMainModule(mainModuleName: String) = {
    DefinitionTransformer(
      module =>
        if (module.name != mainModuleName || !module.importedModuleNames.contains("STRATEGY")) {
          module
        } else {
          Module(module.name, module.imports, module.localSentences + Rule(
            KORE.KApply(KLabels.STRATEGY_CELL,
              KORE.KApply(KLabels.NO_DOTS),
              KORE.KRewrite(
                KORE.KVariable("S", Att.empty.add(classOf[Sort], Sorts.KItem)),
                KORE.KSequence(
                  KORE.KApply(KORE.KLabel("#STUCK")),
                  KORE.KVariable("S", Att.empty.add(classOf[Sort], Sorts.KItem)),
                )
              ),
              KORE.KApply(KLabels.DOTS)
            ),
            KORE.KApply(
              KLabels.NOT_EQUALS_K, 
              KORE.KVariable("S", Att.empty.add(classOf[Sort], Sorts.KItem)),
              KORE.KApply(KORE.KLabel("#STUCK")),
            ),
            BooleanUtils.TRUE,
            Att.empty.add(Att.OWISE)
          ), module.att)
        }
    )
  }
}

class ContainsSCell extends ExistsK {
  override def apply(k: KApply): java.lang.Boolean = {
    k.klabel == KLabels.STRATEGY_CELL || super.apply(k)
  }
}

class Strategy() {
  import Strategy._

  def addStrategyCellToRulesTransformer(defn: Definition) =
    DefinitionTransformer(
      ModuleTransformer.fromSentenceTransformer({
        (module, r) =>
          val rich = kore.Rich(module)

          def isFunctionRhs(body: kore.K): Boolean = {
            RewriteToTop.toRight(body) match {
              case KApply(klabel, _) if module.attributesFor.contains(klabel) && module.attributesFor(klabel).contains(Att.FUNCTION) => true
              case _ => false
            }
          }

          import rich._
          
          if (!defn.mainModule.importedModuleNames.contains("STRATEGY") || r.att.contains(Att.ANYWHERE) || r.att.contains(Att.MACRO) || r.att.contains(Att.ALIAS) || r.att.contains(Att.MACRO_REC) || r.att.contains(Att.ALIAS_REC)) {
            r
          } else
            r match {
              case r: Rule if !new ContainsSCell().apply(r.body) =>
                val newBody = RewriteToTop.toLeft(r.body) match {
                  case KApply(klabel, _) if !isFunctionRhs(r.body) && (!module.attributesFor.contains(klabel) || !module.attributesFor(klabel).contains(Att.FUNCTION)) =>
                    // todo: "!module.attributesFor.contains(klabel) ||" when #1723 is fixed

                    def makeRewrite(tag: String) =
                      KORE.KSequence(
                        KORE.KRewrite(
                          KORE.KApply(KORE.KLabel("#applyRule"), KORE.KToken(tag, KORE.Sort("#RuleTag"))),
                          KORE.KApply(KORE.KLabel("#appliedRule"), KORE.KToken(tag, KORE.Sort("#RuleTag")))),
                        KORE.KVariable("SREST"))

                    val strategy =
                      if (r.att.contains(Att.TAG)) {
                        makeRewrite(r.att.get(Att.TAG))
                      } else {
                        makeRewrite("regular")
                      }

                    KORE.KApply(KLabels.CELLS, r.body,
                      KORE.KApply(KLabels.STRATEGY_CELL,
                        KORE.KApply(KLabels.NO_DOTS),
                        strategy,
                        KORE.KApply(KLabels.NO_DOTS)
                      ))
                  case _ => r.body
                }
                Rule(newBody, r.requires, r.ensures, r.att)
              case r => r
            }
      }, "add strategy cell to rules"))

}
