// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

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
        private final Set<Variable> rhsOnlyVariables;

        public Entry(ConjunctiveFormula formula, boolean patternFolding, boolean partialSimplification,
                     ConjunctiveFormula constraint,
                     Set<Variable> rhsOnlyVariables) {
            this.formula = formula;
            this.patternFolding = patternFolding;
            this.partialSimplification = partialSimplification;
            this.constraint = constraint;
            this.rhsOnlyVariables = rhsOnlyVariables;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Entry entry = (Entry) o;
            return patternFolding == entry.patternFolding &&
                    partialSimplification == entry.partialSimplification &&
                    formula.equals(entry.formula) &&
                    Objects.equals(constraint, entry.constraint) &&
                    rhsOnlyVariables.equals(entry.rhsOnlyVariables);
        }

        @Override
        public int hashCode() {
            return Objects.hash(formula, patternFolding, partialSimplification, constraint, rhsOnlyVariables);
        }
    }

    private Map<Entry, ConjunctiveFormula> evaluationCache = new HashMap<>();

    public ConjunctiveFormula cacheGet(ConjunctiveFormula formula, boolean patternFolding,
                                       boolean partialSimplification,
                                       Set<Variable> rhsOnlyVariables,
                                       TermContext context) {
        return context.global().javaExecutionOptions.cacheFormulas
               ? evaluationCache
                       .get(new Entry(formula, patternFolding, partialSimplification, context.getTopConstraint(),
                               rhsOnlyVariables))
               : null;
    }

    public void cachePut(ConjunctiveFormula formula, boolean patternFolding, boolean partialSimplification,
                         TermContext context, Set<Variable> rhsOnlyVariables,
                         ConjunctiveFormula result) {
        if (context.global().javaExecutionOptions.cacheFormulas) {
            evaluationCache.put(
                    new Entry(formula, patternFolding, partialSimplification, context.getTopConstraint(),
                            rhsOnlyVariables), result);
            evaluationCache.put(
                    new Entry(result, patternFolding, partialSimplification, context.getTopConstraint(),
                            rhsOnlyVariables), result);
        }
    }

    public void clear() {
        evaluationCache.clear();
    }

    public int size() {
        return evaluationCache.size();
    }
}
