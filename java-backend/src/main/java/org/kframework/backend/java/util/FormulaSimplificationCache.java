// Copyright (c) 2013-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

/**
 * @author Denis Bogdanas
 * Created on 11-Nov-18.
 */
public class FormulaSimplificationCache {

    private class Entry {
        private final ConjunctiveFormula formula;
        private final boolean patternFolding;
        private final boolean partialSimplification;
        private final ConjunctiveFormula constraint;

        public Entry(ConjunctiveFormula formula, boolean patternFolding, boolean partialSimplification,
                     ConjunctiveFormula constraint) {
            this.formula = formula;
            this.patternFolding = patternFolding;
            this.partialSimplification = partialSimplification;
            this.constraint = constraint;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof Entry)) return false;
            Entry entry = (Entry) o;
            return patternFolding == entry.patternFolding &&
                    partialSimplification == entry.partialSimplification &&
                    Objects.equals(formula, entry.formula) &&
                    Objects.equals(constraint, entry.constraint);
        }

        @Override
        public int hashCode() {
            return Objects.hash(formula, patternFolding, partialSimplification, constraint);
        }
    }

    private Map<Entry, ConjunctiveFormula> evaluationCache = new HashMap<>();

    public ConjunctiveFormula cacheGet(ConjunctiveFormula formula, boolean patternFolding,
                                       boolean partialSimplification, TermContext context) {
        return context.global().globalOptions.cacheFunctions
                ? evaluationCache.get(new Entry(formula, patternFolding, partialSimplification, context.getTopConstraint()))
                : null;
    }

    public void cachePut(ConjunctiveFormula formula, boolean patternFolding, boolean partialSimplification,
                         TermContext context, ConjunctiveFormula result) {
        if (context.global().globalOptions.cacheFunctions) {
            evaluationCache.put(new Entry(formula, patternFolding, partialSimplification, context.getTopConstraint()), result);
            evaluationCache.put(new Entry(result, patternFolding, partialSimplification, context.getTopConstraint()), result);
        }
    }
}
