package org.kframework

import org.kframework.attributes.Att
import org.kframework.builtin.BooleanUtils
import org.kframework.builtin.KLabels
import org.kframework.builtin.Sorts
import org.kframework.compile.RewriteToTop
import org.kframework.definition.{DefinitionTransformer, ModuleTransformer, Module, Sentence, Rule, Definition}
import org.kframework.kore.ExistsK
import org.kframework.kore.KApply
import org.kframework.kore.KLabel
import org.kframework.kore.KORE
import org.kframework.kore.Sort
import org.kframework.kore.Unapply.{KApply, KLabel}

object Strategy {
  val strategyCellName = "<s>"
  val strategyCellLabel = KORE.KLabel(strategyCellName)

  def addStrategyRuleToMainModule(mainModuleName: String) = {
    DefinitionTransformer(
      module =>
        if (module.name != mainModuleName || !module.importedModuleNames.contains("STRATEGY$SYNTAX")) {
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
            Att.empty.add("owise")
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

class Strategy(heatCool: Boolean, superstrict: Boolean) {
  import Strategy._

  private def isFunctionRhs(body: kore.K, module: Module): Boolean = {
    RewriteToTop.toRight(body) match {
      case KApply(klabel, _) if module.attributesFor.contains(klabel) && module.attributesFor(klabel).contains(Att.Function) => true
      case _ => false
    }
  }

  private def isBadRule(r: Sentence) =
    r.att.contains("anywhere") || r.att.contains("macro") || r.att.contains("alias") || r.att.contains("macro-rec") || r.att.contains("alias-rec")

  private def isGoodLHS(r: Rule, module: Module, klabel: KLabel, defn: Definition) =
    !isFunctionRhs(r.body, module) && (!defn.mainModule.attributesFor.contains(klabel) || !defn.mainModule.attributesFor(klabel).contains(Att.Function))

  def addProgressCellToRulesTransformer(defn: Definition) =
    DefinitionTransformer(
      ModuleTransformer.fromSentenceTransformer({
        (module, r) =>
          val rich = kore.Rich(module)

          import rich._

          if (!superstrict || isBadRule(r)) {
            r
          } else {
            r match {
              case r: Rule =>
                def makeRewrite(att: Att) = {
                  if (att.contains("heat")) {
                    KORE.KRewrite(KORE.KVariable("_Progress", Att.empty.add(classOf[Sort], Sorts.Bool)), KORE.KToken("false", Sorts.Bool))
                  } else if (att.contains("cool")) {
                    KORE.KToken("true", Sorts.Bool)
                  } else {
                    KORE.KRewrite(KORE.KVariable("_Progress", Att.empty.add(classOf[Sort], Sorts.Bool)), KORE.KToken("true", Sorts.Bool))
                  }
                }
    
                val newBody = RewriteToTop.toLeft(r.body) match {
                  case KApply(klabel, _) if isGoodLHS(r, module, klabel, defn) =>
                        KORE.KApply(KLabels.CELLS, r.body,
                          KORE.KApply(KLabels.GENERATED_PROGRESS_CELL,
                            KORE.KApply(KLabels.NO_DOTS),
                            makeRewrite(r.att),
                            KORE.KApply(KLabels.NO_DOTS)
                          ))
                  case _ => r.body
                }
                Rule(newBody, r.requires, r.ensures, r.att)
              case _ => r
            }
          }
      }, "add strategy cell to rules"))



          
  def addStrategyCellToRulesTransformer(defn: Definition) =
    DefinitionTransformer(
      ModuleTransformer.fromSentenceTransformer({
        (module, r) =>
          val rich = kore.Rich(module)

          import rich._
          
          if (!defn.mainModule.importedModuleNames.contains("STRATEGY$SYNTAX") || isBadRule(r)) {
            r
          } else
            r match {
              case r: Rule if !new ContainsSCell().apply(r.body) =>
                val newBody = RewriteToTop.toLeft(r.body) match {
                  case KApply(klabel, _) if isGoodLHS(r, module, klabel, defn) =>
                    // todo: "!module.attributesFor.contains(klabel) ||" when #1723 is fixed

                    def makeRewrite(tag: String) =
                      KORE.KSequence(
                        KORE.KRewrite(
                          KORE.KApply(KORE.KLabel("#applyRule"), KORE.KToken(tag, KORE.Sort("#RuleTag"))),
                          KORE.KApply(KORE.KLabel("#appliedRule"), KORE.KToken(tag, KORE.Sort("#RuleTag")))),
                        KORE.KVariable("SREST"))

                    val strategy =
                      if (r.att.contains("tag")) {
                        makeRewrite(r.att.get("tag"))
                      } else if (heatCool && r.att.contains(Att.heat)) {
                        makeRewrite("heat")
                      } else if (heatCool && r.att.contains(Att.cool)) {
                        makeRewrite("cool")
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
