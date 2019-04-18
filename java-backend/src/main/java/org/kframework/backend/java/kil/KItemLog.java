// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.util.RuleSourceUtil;
import org.kframework.utils.IndentingFormatter;

import java.util.ArrayList;
import java.util.Collections;

/**
 * @author Denis Bogdanas
 * Created on 07-Apr-19.
 */
public class KItemLog {
    private KItemLog() {}

    private static ArrayList<String> indents = new ArrayList<>(Collections.singleton(""));

    public static synchronized String indent(int n) {
        if (!(n < indents.size())) {
            for (int i = indents.size(); i <= n; i++) {
                indents.add(indents.get(i - 1) + "  ");
            }
        }
        return indents.get(n);
    }

    static void logBuiltinEval(KLabelConstant kLabelConstant, int nestingLevel, GlobalContext global) {
        if (global.javaExecutionOptions.logRulesPublic) {
            global.log().format("\nKItem lvl %d, %23s: %s\n",
                    nestingLevel, "builtin evaluation", kLabelConstant);
        }
    }

    static void logStartingEval(KLabelConstant kLabelConstant, int nestingLevel, GlobalContext global,
                                TermContext termContext) {
        if (global.javaExecutionOptions.logRulesPublic) {
            if (nestingLevel == 1) {
                global.log().format("\n-------------------------");
            }
            global.log().format("\nKItem lvl %d, %23s: %s\n",
                    nestingLevel, "starting evaluation", kLabelConstant);
            if (termContext.getTopConstraint() == null) {
                global.log().format("%13s%23s  null constraint\n", "", "");
            }
        }
    }

    static void logApplyingFuncRule(KLabelConstant kLabelConstant, int nestingLevel,
                                    Rule rule, GlobalContext global) {
        if (global.javaExecutionOptions.logRulesPublic) {
            global.log().format("\n KItem lvl %d, %23s: %s, source: %s %s\n",
                    nestingLevel, "function rule applying", kLabelConstant, rule.getSource(), rule.getLocation());
        }
    }

    public static void logEvaluatingConstraints(Term term, int nestingLevel,
                                                Rule rule, GlobalContext global, String logMsg) {
        if (global.javaExecutionOptions.logRulesPublic) {
            org.kframework.kore.KLabel kLabel = term instanceof KItem ? ((KItem) term).klabel() : null;
            //one extra space for indent
            global.log().format(" -------------\n");
            global.log().format(" %s lvl %d, %23s: %s, source: %s %s\n", logMsg,
                    nestingLevel, "matched, eval. constr.", kLabel, rule.getSource(), rule.getLocation());
        }
    }

    static void logRuleApplied(KLabelConstant kLabelConstant, int nestingLevel,
                               boolean resultNotNull, Rule rule, GlobalContext global) {
        if (global.javaExecutionOptions.logRulesPublic) {
            String msg = resultNotNull ? "rule applied" : "rule application failed";
            logRuleApplying(kLabelConstant, nestingLevel, rule, msg, global);
        }
    }

    static void logEvaluated(KItem kItem, Term result, int nestingLevel) {
        logEvaluatedImpl(kItem, result, nestingLevel, "evaluated");
    }

    static void logEvaluatedOwise(KItem kItem, Term owiseResult, int nestingLevel) {
        logEvaluatedImpl(kItem, owiseResult, nestingLevel, "evaluated (owise)");
    }

    static void logNoRuleApplicable(KItem kItem, int nestingLevel) {
        if (kItem.globalContext().javaExecutionOptions.logFunctionEvalPublic) {
            kItem.globalContext().log().format("KItem lvl %d, %23s: %s\n",
                    nestingLevel, "no rule applicable", kItem);
        }
    }

    private static void logEvaluatedImpl(KItem kItem, Term result, int nestingLevel, String evaluated) {
        if (kItem.globalContext().javaExecutionOptions.logRulesPublic) {
            String formatStr = "" +
                    "KItem lvl %d, %23s: %s\n"
                    + "             %23s: %s\n";
            IndentingFormatter log = kItem.globalContext().log();
            if (kItem.globalContext().javaExecutionOptions.logFunctionEvalPublic) {
                log.format(formatStr, nestingLevel, evaluated, kItem, "to", result);
            } else {
                log.format(formatStr, nestingLevel, evaluated, kItem.klabel(),
                        "to", result instanceof KItem ? ((KItem) result).klabel() : result);
            }
        }
    }

    static void logAnywhereRule(KLabelConstant kLabelConstant, int nestingLevel, Rule rule, GlobalContext global) {
        if (global.javaExecutionOptions.logRulesPublic) {
            global.newLogIndent(indent(nestingLevel - 1) + " ");
            try {
                logRuleApplying(kLabelConstant, nestingLevel, rule, "anywhere rule applied", global);
            } finally {
                global.restorePreviousLogIndent();
            }
        }
    }

    private static void logRuleApplying(KLabelConstant kLabelConstant, int nestingLevel, Rule rule, String msg,
                                        GlobalContext global) {
        global.log().format("\n KItem lvl %d, %23s: %s\n", nestingLevel, msg, kLabelConstant);
        RuleSourceUtil.appendRuleAndSource(rule, global.log());
    }
}
