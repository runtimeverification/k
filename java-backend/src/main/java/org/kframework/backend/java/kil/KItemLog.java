// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.util.RuleSourceUtil;

/**
 * @author Denis Bogdanas
 * Created on 07-Apr-19.
 */
public class KItemLog {
    private KItemLog() {}

    static void logBuiltinEval(KLabelConstant kLabelConstant, int nestingLevel, GlobalContext global) {
        if (global.javaExecutionOptions.logRulesPublic) {
            System.err.format("\nKItem lvl %d, %23s: %s\n",
                    nestingLevel, "builtin evaluation", kLabelConstant);
        }
    }

    static void logStartingEval(KLabelConstant kLabelConstant, int nestingLevel, GlobalContext global) {
        if (global.javaExecutionOptions.logRulesPublic) {
            if (nestingLevel == 1) {
                System.err.print("\n-------------------------");
            }
            System.err.format("\nKItem lvl %d, %23s: %s\n",
                    nestingLevel, "starting evaluation", kLabelConstant);
        }
    }

    static void logApplyingFuncRule(KLabelConstant kLabelConstant, int nestingLevel,
                                    Rule rule, GlobalContext global) {
        if (global.javaExecutionOptions.logRulesPublic) {
            System.err.format("\nKItem lvl %d, %23s: %s, source: %s\n",
                    nestingLevel, "function rule applying", kLabelConstant, rule.getSource());
        }
    }

    static void logRuleApplied(KLabelConstant kLabelConstant, int nestingLevel,
                               boolean resultNotNull, Rule rule, GlobalContext global) {
        if (global.javaExecutionOptions.logRulesPublic) {
            String msg = resultNotNull ? "rule applied" : "rule application failed";
            logRuleApplying(kLabelConstant, nestingLevel, rule, msg);
        }
    }

    static void logEvaluated(KItem kItem, Term result, int nestingLevel) {
        logEvaluatedImpl(kItem, result, nestingLevel, "evaluated");
    }

    static void logEvaluatedOwise(KItem kItem, Term owiseResult, int nestingLevel) {
        logEvaluatedImpl(kItem, owiseResult, nestingLevel, "evaluated (owise)");
    }

    static void logNoRuleApplicable(KItem kItem, int nestingLevel) {
        if (kItem.globalContext().javaExecutionOptions.logFunctionTargetPublic) {
            System.err.format("KItem lvl %d, %23s: %s\n", nestingLevel, "no rule applicable", kItem);
        }
    }

    private static void logEvaluatedImpl(KItem kItem, Term result, int nestingLevel, String evaluated) {
        if (kItem.globalContext().javaExecutionOptions.logRulesPublic) {
            String formatStr = "" +
                    "KItem lvl %d, %23s: %s\n"
                    + "             %23s: %s\n";
            if (kItem.globalContext().javaExecutionOptions.logFunctionTargetPublic) {
                System.err.format(formatStr, nestingLevel, evaluated, kItem, "to", result);
            } else {
                System.err.format(formatStr, nestingLevel, evaluated, kItem.klabel(), "to",
                        result instanceof KItem ? ((KItem) result).klabel() : result);
            }
        }
    }

    static void logAnywhereRule(KLabelConstant kLabelConstant, int nestingLevel, Rule rule, GlobalContext global) {
        if (global.javaExecutionOptions.logRulesPublic) {
            logRuleApplying(kLabelConstant, nestingLevel, rule, "anywhere rule applied");
        }
    }

    private static void logRuleApplying(KLabelConstant kLabelConstant, int nestingLevel, Rule rule, String msg) {
        System.err.format("\nKItem lvl %d, %23s: %s\n", nestingLevel, msg, kLabelConstant);
        RuleSourceUtil.printRuleAndSource(rule);
    }
}
