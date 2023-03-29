// Copyright (c) K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.DisjunctiveFormula;
import org.kframework.backend.java.symbolic.Equality;
import org.kframework.backend.java.symbolic.FastRuleMatcher;
import org.kframework.backend.java.symbolic.PatternExpander;
import org.kframework.backend.java.symbolic.PersistentUniqueList;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Constants;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.Triple;
import org.kframework.backend.java.util.FormulaContext;


/**
 * A K term associated with symbolic constraints.
 *
 * @author AndreiS
 */
public class ConstrainedTerm extends JavaSymbolicObject {

    public static class Data {
        public final Term term;
        public final ConjunctiveFormula constraint;

        public Data(Term term, ConjunctiveFormula constraint) {
            super();
            this.term = term;
            this.constraint = constraint;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((constraint == null) ? 0 : constraint.hashCode());
            result = prime * result + ((term == null) ? 0 : term.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            Data other = (Data) obj;
            if (constraint == null) {
                if (other.constraint != null)
                    return false;
            } else if (!constraint.equals(other.constraint))
                return false;
            if (term == null) {
                if (other.term != null)
                    return false;
            } else if (!term.equals(other.term))
                return false;
            return true;
        }

    }

    private final Data data;

    private final TermContext context;

    public ConstrainedTerm(Term term, ConjunctiveFormula constraint, TermContext context) {
        this.data = new Data(term, constraint);
        this.context = context;
        this.context.setTopTerm(term);
    }

    public ConstrainedTerm(Term term, TermContext context) {
        this(term, ConjunctiveFormula.of(context.global()), context);
    }

    public TermContext termContext() {
        return context;
    }

    public ConjunctiveFormula constraint() {
        return data.constraint;
    }

    public boolean implies(ConstrainedTerm constrainedTerm, Rule specRule, boolean logFailures) {
        ConjunctiveFormula conjunctiveFormula = matchImplies(constrainedTerm, true, logFailures,
                new FormulaContext(FormulaContext.Kind.FinalImplication, specRule, constrainedTerm.context.global()),
                specRule.matchingSymbols());
        return conjunctiveFormula != null;
    }

    public ConstrainedTerm expandPatterns(boolean narrowing) {
        ConstrainedTerm result = this;
        while (true) {
            PatternExpander patternExpander = new PatternExpander(
                    result.constraint(),
                    narrowing,
                    context);
            ConstrainedTerm expandedTerm = (ConstrainedTerm) result.accept(patternExpander);
            if (expandedTerm == result) {
                break;
            }
            result = new ConstrainedTerm(
                    expandedTerm.term().substituteAndEvaluate(patternExpander.extraConstraint().substitution(), context),
                    expandedTerm.constraint().add(patternExpander.extraConstraint()).simplify(context),
                    context);
        }

        return result;
    }

    /**
     * Checks if {@code this} implies {@code matchRHSTerm}, assuming the variables
     * occurring only in {@code matchRHSTerm} (but not in {@code this}) are
     * existentially quantified.
     *
     * @return If implication value is {@code true}, return the unification constraint:
     * implicationLHS /\ implicationRHS. Otherwise return {@code true}.
     */
    public ConjunctiveFormula matchImplies(ConstrainedTerm matchRHSTerm, boolean expand, boolean logFailures,
                                           FormulaContext formulaContext, Set<String> matchingSymbols) {
        context.setTopConstraint(data.constraint);
        try {
            ConjunctiveFormula constraint = ConjunctiveFormula.of(matchRHSTerm.termContext().global())
                    .add(data.constraint.substitution())
                    .add(data.term, matchRHSTerm.data.term)
                    .add(matchRHSTerm.data.constraint);
            Set<Variable> matchRHSOnlyVars = Sets.difference(constraint.variableSet(),
                    Sets.union(variableSet(), termContext().getInitialLhsVariables()));
            constraint = constraint.simplifyBeforePatternFolding(context, matchRHSOnlyVars, logFailures);
            if (constraint.isFalseExtended()) {
                formulaContext.printImplicationExitPoint(constraint, 1);
                return null;
            }

            constraint = constraint.applyProjectionLemma();
            if (constraint.isFalse()) {
                formulaContext.printImplicationExitPoint(constraint, 2);
                return null;
            }

            if (matchingSymbols != null) {
                constraint = constraint.resolveMatchingSymbols(matchingSymbols);
                if (constraint.isFalse()) {
                    formulaContext.printImplicationExitPoint(constraint, 3);
                    return null;
                }
            }

            /* apply pattern folding */
            constraint = constraint.simplifyModuloPatternFolding(context, matchRHSOnlyVars);
            if (constraint.isFalse()) {
                formulaContext.printImplicationExitPoint(constraint, 4);
                return null;
            }

            formulaContext.printTargetFormula(constraint);

            if (expand) {
                constraint = constraint.expandPatterns(false, context)
                        .simplifyModuloPatternFolding(context, matchRHSOnlyVars);
                if (constraint.isFalse()) {
                    return null;
                }
            }

            // evaluate/simplify equalities
            for (Equality equality : constraint.equalities()) {
                Term equalityTerm = equality.toK();
                Term evaluatedTerm = equalityTerm.evaluate(context);
                if (!evaluatedTerm.equals(equalityTerm)) {
                    constraint = constraint.addAll(Collections.singletonList(evaluatedTerm));
                    if (constraint == null || constraint.isFalse()) {
                        return null;
                    }
                }
            }
            constraint = constraint.simplifyModuloPatternFolding(context, matchRHSOnlyVars);
            if (constraint.isFalse()) {
                return null;
            }

            constraint = (ConjunctiveFormula) constraint.evaluate(context);

            constraint = constraint.orientSubstitution(matchRHSOnlyVars);

            ConjunctiveFormula implicationLHS = data.constraint;
            ConjunctiveFormula implicationRHS = constraint.removeSubstitutionVars(matchRHSOnlyVars);
            implicationRHS =
                    (ConjunctiveFormula) implicationRHS.substituteAndEvaluate(implicationLHS.substitution(), context);

            boolean implies = implicationLHS.implies(implicationRHS, matchRHSOnlyVars, formulaContext);
            if (!implies) {
                return null;
            }

            return data.constraint.addAndSimplify(constraint, context);
        } finally {
            context.setTopConstraint(null);
        }
    }

    public Term term() {
        return data.term;
    }

    /**
     * Unifies this constrained term with another constrained term. Returns a list of solutions for the unification problem.
     * Each solution is a triple of (1) the unification constraint, (2) whether the constraint is a matching of the variables of the argument constrainedTerm,
     * and (3) the inner rewrites from the constrainedTerm.
     */
    public List<Triple<ConjunctiveFormula, Boolean, Map<scala.collection.immutable.List<Pair<Integer, Integer>>, Term>>> unify(
            ConstrainedTerm constrainedTerm,
            Set<Variable> variables, FormulaContext formulaContext) {
        /* unify the subject term and the pattern term without considering those associated constraints */
        ConjunctiveFormula unificationConstraint = FastRuleMatcher.unify(term(), constrainedTerm.term(), context);
        if (unificationConstraint.isFalse()) {
            return Collections.emptyList();
        }
        unificationConstraint = unificationConstraint.simplify(context);
        if (unificationConstraint.isFalse()) {
            return Collections.emptyList();
        }

        return evaluateConstraints(
                unificationConstraint,
                constraint(),
                constrainedTerm.constraint(),
                variables == null ? constrainedTerm.variableSet() : variables,
                context, formulaContext);
    }

    public static List<Triple<ConjunctiveFormula, Boolean, Map<scala.collection.immutable.List<Pair<Integer, Integer>>, Term>>> evaluateConstraints(
            ConjunctiveFormula constraint,
            ConjunctiveFormula subjectConstraint,
            ConjunctiveFormula patternConstraint,
            Set<Variable> variables,
            TermContext context, FormulaContext formulaContext) {
        context.setTopConstraint(subjectConstraint);
        List<ConjunctiveFormula> candidates = constraint.getDisjunctiveNormalForm().conjunctions().stream()
                .map(c -> c.addAndSimplify(patternConstraint, context))
                .filter(c -> !c.isFalse())
                .map(ConjunctiveFormula::resolveNonDeterministicLookups)
                .map(ConjunctiveFormula::getDisjunctiveNormalForm)
                .map(DisjunctiveFormula::conjunctions)
                .flatMap(List::stream)
                .map(c -> c.simplify(context))
                .filter(c -> !c.isFalse())
                .collect(Collectors.toList());

        List<Triple<ConjunctiveFormula, Boolean, Map<scala.collection.immutable.List<Pair<Integer, Integer>>, Term>>> solutions = Lists.newArrayList();
        for (ConjunctiveFormula candidate : candidates) {
            candidate = candidate.orientSubstitution(variables);

            Pair<Map<scala.collection.immutable.List<Pair<Integer, Integer>>, Term>, ConjunctiveFormula> pair = ConstrainedTerm.splitRewrites(candidate);
            ConjunctiveFormula candidateConstraint = pair.getRight();

            ConjunctiveFormula solution = candidateConstraint.addAndSimplify(subjectConstraint, context);

            if (solution.isFalseExtended()) {
                continue;
            }

            /* OPTIMIZATION: if no narrowing happens, the constraint remains unchanged;
             * thus, there is no need to check satisfiability or expand patterns */
            boolean isMatching = candidate.isMatching(variables);

            if (!isMatching && solution.checkUnsat(
                    //formulaContext param is intended for implication. We have to create a new one here.
                    new FormulaContext(FormulaContext.implicationToConstrKind.get(formulaContext.kind),
                            formulaContext.rule, context.global()))) {
                continue;
            }

            /* OPTIMIZATION: If the new constraint is implied by existing assumptions,
               then we do not need to add any formulas.
               It may still be necessary to add substitutions resulting from matching,
               so we do still add the equalities from the candidate constraint.
               We assume it will be uncommon to have multiple candidate solutions in this
               category, so we don't bother trying to deduplicate here.
               (bmmoore): I don't know whether it's actually possible for two candidate
                  constraints to both fall under this optimization but to have equalities
                  that induce different results.
             */
            assert solution.disjunctions().isEmpty();
            if (candidate.substitution().keySet().equals(variables)
                    && !candidate.isSubstitution()
                    && subjectConstraint.implies(ConjunctiveFormula.of(context.global())
                    .addAll(candidateConstraint.equalities()), Sets.newHashSet(), formulaContext)) {
                solutions.add(Triple.of(
                        subjectConstraint
                                .addAndSimplify(candidateConstraint.substitution(), context)
                                .orientSubstitution(variables),
                        true,
                        pair.getLeft()));
            } else {
                solutions.add(Triple.of(solution, isMatching, pair.getLeft()));
            }
        }

        return solutions;
    }

    /**
     * Splits the constraint into the rewrites and the "pure" constraint.
     * {@link FastRuleMatcher} encodes the information about the inner rewrites (path to rewrite and what to rewrite to) as a boolean predicate in the constraint.
     * This method method reverses the encoding.
     */
    private static Pair<Map<scala.collection.immutable.List<Pair<Integer, Integer>>, Term>, ConjunctiveFormula> splitRewrites(ConjunctiveFormula constraint) {
        Map<Boolean, List<Equality>> split = constraint.equalities().stream()
                .collect(Collectors.partitioningBy(e -> e.leftHandSide() instanceof LocalRewriteTerm));
        Map<scala.collection.immutable.List<Pair<Integer, Integer>>, Term> rewrites = split.get(true).stream()
                .map(Equality::leftHandSide)
                .map(LocalRewriteTerm.class::cast)
                .collect(Collectors.toMap(e -> e.path, e -> e.rewriteRHS));
        ConjunctiveFormula pureConstraint = ConjunctiveFormula.of(
                constraint.substitution(),
                PersistentUniqueList.from(split.get(false)),
                constraint.disjunctions(),
                constraint.globalContext());
        return Pair.of(rewrites, pureConstraint);
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof ConstrainedTerm)) {
            return false;
        }

        ConstrainedTerm constrainedTerm = (ConstrainedTerm) object;
        return data.equals(constrainedTerm.data);
    }

    @Override
    public int hashCode() {
        int h = hashCode;
        if (h == Constants.NO_HASHCODE) {
            h = 1;
            h = h * Constants.HASH_PRIME + data.hashCode();
            h = h == 0 ? 1 : h;
            hashCode = h;
        }
        return h;
    }

    @Override
    public String toString() {
        return data.term + ConjunctiveFormula.SEPARATOR + data.constraint;
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }
}
