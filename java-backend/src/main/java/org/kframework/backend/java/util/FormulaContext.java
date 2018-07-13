// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import com.google.common.collect.ImmutableMap;
import org.kframework.attributes.Location;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.util.Collections;
import java.util.HashMap;
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

    public FormulaContext(Kind kind, Rule rule) {
        this.kind = kind;
        this.rule = rule;
        this.z3Profiler = rule.globalContext().profiler.z3Profilers.get(kind);
    }

    public void printImplication(ConjunctiveFormula left, ConjunctiveFormula right, Boolean proved, boolean cached) {
        if (proved) {
            System.err.format("\nZ3 Implication (%s) RHS proved: %s\n", kind.label, right);
        } else {
            System.err.format("\nZ3 Implication (%s) failed:\n\t%s\n  implies \n\t%s\n", kind.label, left, right);
        }
        if (cached) {
            System.err.println("cached result");
        }
        File source = rule.source().isPresent() ? new File(rule.getSource().source()) : null;
        System.err.format("\nSource: %s %s\n", source, rule.getLocation());
        if (sourceShortEnough(rule)) {
            System.err.println(loadSource(rule));
        }
        System.err.println("==================================");
    }

    public void printUnsat(ConjunctiveFormula formula, boolean unsat, boolean cached) {
        if (unsat) {
            System.err.format("\nZ3 Constraint (%s) is unsat: %s\n", kind.label, formula);
        } else {
            System.err.format("\nZ3 Constraint (%s) is assumed sat: %s\n", kind.label, formula);
        }
        if (cached) {
            System.err.println("cached result");
        }
        File source = rule.source().isPresent() ? new File(rule.getSource().source()) : null;
        System.err.format("\nSource: %s %s\n", source, rule.getLocation());
        if (sourceShortEnough(rule)) {
            System.err.println(loadSource(rule));
        }
        System.err.println("==================================");
    }

    private boolean sourceShortEnough(Rule rule) {
        Location location = rule.getLocation();
        return location != null && location.endLine() - location.startLine() <= 20;
    }

    private static final Map<Rule, String> cache = Collections.synchronizedMap(new HashMap<>());

    private String loadSource(Rule rule) {
        if (!cache.containsKey(rule)) {
            if (rule.getSource() != null && rule.getLocation() != null) {
                cache.put(rule, FileUtil.loadFragment(new File(rule.getSource().source()), rule.getLocation()));
            }
        }
        return cache.get(rule);
    }
}
