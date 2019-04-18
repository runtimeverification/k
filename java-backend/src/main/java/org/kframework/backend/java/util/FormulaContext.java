// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.collect.ImmutableMap;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.utils.IndentingFormatter;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.Map;

/**
 * The context that generated a certain ConjunctiveFormula, for debugging/profiling purposes.
 *
 * @author Denis Bogdanas
 * Created on 28-Jul-18.
 */
public class FormulaContext {

    public enum Kind {
        RegularRule("Regular rule implication"),
        FunctionRule("Function rule implication"),
        SpecRule("Spec rule implication"),
        OwiseRule("Owise rule implication"),
        EquivImplication("Equiv check implication"),
        PatternRule("Pattern rule implication"),
        FinalImplication("Final implication"),

        RegularConstr("Regular rule constraint"),
        FunctionConstr("Function rule constraint"),
        SpecConstr("Spec rule constraint"),
        OwiseConstr("Owise rule constraint"),
        EquivConstr("Equiv check constraint"),
        PatternConstr("Pattern rule constraint"),
        PatternBuildResConstr("Pattern build res constraint");

        public final String label;

        Kind(String label) {
            this.label = label;
        }
    }

    public static Map<Kind, Kind> implicationToConstrKind = new ImmutableMap.Builder<Kind, Kind>()
            .put(Kind.RegularRule, Kind.RegularConstr)
            .put(Kind.FunctionRule, Kind.FunctionConstr)
            .put(Kind.SpecRule, Kind.SpecConstr)
            .put(Kind.OwiseRule, Kind.OwiseConstr)
            .put(Kind.EquivImplication, Kind.EquivConstr)
            .put(Kind.PatternRule, Kind.PatternConstr)
            .build();

    public final Kind kind;
    public final Rule rule;
    public Z3Profiler z3Profiler;
    private boolean queryBuildFailure;

    /**
     * @param globalContext - do not use it for logging, only for getting the profiler!
     */
    public FormulaContext(Kind kind, @Nullable Rule rule, @Nonnull GlobalContext globalContext) {
        this.kind = kind;
        this.rule = rule;
        this.z3Profiler = globalContext.profiler.z3Profilers.get(kind);
    }

    public void queryBuildFailure() {
        z3Profiler.newQueryBuildFailure();
        queryBuildFailure = true;
    }

    public void printImplication(ConjunctiveFormula left, ConjunctiveFormula right, Boolean proved, boolean cached) {
        IndentingFormatter log = left.globalContext().log();
        String cachedMsg = cached ? " (cached result)" : "";
        if (queryBuildFailure) {
            log.format("\nZ3 Implication (%s) RHS dropped (cannot be proved)%s:\n%s\n", kind.label, cachedMsg,
                    right.toStringMultiline());
        } else if (proved) {
            log.format("\nZ3 Implication (%s) RHS proved%s:\n%s\n", kind.label, cachedMsg, right.toStringMultiline());
        } else {
            log.format("\nZ3 Implication (%s) failed%s:\n%s\n  implies\n%s\n",
                    kind.label, cachedMsg, left.toStringMultiline(), right.toStringMultiline());
        }
        if (rule != null) {
            log.format("\nRule for formula above:\n");
            RuleSourceUtil.appendRuleAndSource(rule, log);
        }
        log.format("-------------\n");
    }

    public void printUnsat(ConjunctiveFormula formula, boolean unsat, boolean cached) {
        IndentingFormatter log = formula.globalContext().log();
        String cachedMsg = cached ? " (cached result)" : "";
        if (unsat) {
            log.format("\nZ3 Constraint (%s) is unsat%s:\n%s\n", kind.label, cachedMsg, formula.toStringMultiline());
        } else {
            log.format("\nZ3 Constraint (%s) is assumed sat%s:\n%s\n", kind.label, cachedMsg,
                    formula.toStringMultiline());
        }
        if (rule != null) {
            log.format("\nRule for formula above:\n");
            RuleSourceUtil.appendRuleAndSource(rule, log);
        }
        log.format("-------------\n");
    }

    public void printTargetFormula(ConjunctiveFormula formula) {
        if (formula.globalContext().javaExecutionOptions.logRulesPublic) {
            IndentingFormatter log = formula.globalContext().log();

            //Removing anonymous vars before printing. They take most of the space but don't influence
            //implication result.
            ConjunctiveFormula formulaToPrint = formula.removeAnonymousSubstitutions();

            log.format("\nImplication (%s) RHS to prove:\n%s\n", kind.label, formulaToPrint.toStringMultiline());
            if (rule != null) {
                log.format("\nRule for formula above:\n");
                RuleSourceUtil.appendRuleAndSource(rule, log);
            }
            log.format("-------------\n");
        }
    }
}
