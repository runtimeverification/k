// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.kframework.backend.java.rewritemachine.MatchingInstruction;
import org.kframework.backend.java.symbolic.AbstractKMachine;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.DisjunctiveFormula;
import org.kframework.backend.java.symbolic.PatternExpander;
import org.kframework.backend.java.symbolic.SymbolicUnifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Constants;
import org.kframework.kil.ASTNode;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import org.apache.commons.lang3.tuple.Pair;


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

    public boolean implies(ConstrainedTerm constrainedTerm) {
        return matchImplies(constrainedTerm, true) != null;
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
     * Checks if this constrained term implies the given constrained term, assuming the variables
     * occurring only in the given constrained term (but not in this constrained term) are
     * existentially quantified.
     */
    public ConjunctiveFormula matchImplies(ConstrainedTerm constrainedTerm, boolean expand) {
        ConjunctiveFormula constraint = ConjunctiveFormula.of(constrainedTerm.termContext().global())
                .add(data.constraint.substitution())
                .add(data.term, constrainedTerm.data.term)
                .simplifyBeforePatternFolding(context);
        if (constraint.isFalse()) {
            return null;
        }

        /* apply pattern folding */
        constraint = constraint.simplifyModuloPatternFolding(context)
                .add(constrainedTerm.data.constraint)
                .simplifyModuloPatternFolding(context);
        if (constraint.isFalse()) {
            return null;
        }

        if (expand) {
            constraint = constraint.expandPatterns(false, context).simplifyModuloPatternFolding(context);
            if (constraint.isFalse()) {
                return null;
            }
        }

        context.setTopConstraint(data.constraint);
        constraint = (ConjunctiveFormula) constraint.evaluate(context);

        Set<Variable> rightOnlyVariables = Sets.difference(constraint.variableSet(), variableSet());
        constraint = constraint.orientSubstitution(rightOnlyVariables);

        ConjunctiveFormula leftHandSide = data.constraint;
        ConjunctiveFormula rightHandSide = constraint.removeBindings(rightOnlyVariables);
        rightHandSide = (ConjunctiveFormula) rightHandSide.substitute(leftHandSide.substitution());
        if (!leftHandSide.implies(rightHandSide, rightOnlyVariables)) {
            return null;
        }

        return data.constraint.addAndSimplify(constraint, context);
    }

    public Term term() {
        return data.term;
    }

    /**
     * Unifies this constrained term with another constrained term.
     *
     * @param constrainedTerm
     *            another constrained term
     * @return solutions to the unification problem
     */
    public List<Pair<ConjunctiveFormula, Boolean>> unify(
            ConstrainedTerm constrainedTerm,
            List<MatchingInstruction> instructions,
            Map<CellLabel, Term> cells,
            Set<Variable> variables) {
        assert (instructions == null) == (cells == null);
        /* unify the subject term and the pattern term without considering those associated constraints */
        ConjunctiveFormula constraint;
        if (instructions != null) {
            constraint = AbstractKMachine.unify(this, instructions, cells, termContext());
            if (constraint == null) {
                return Collections.emptyList();
            }
        } else {
            SymbolicUnifier unifier = new SymbolicUnifier(termContext());
            if (!unifier.symbolicUnify(term(), constrainedTerm.term())) {
                return Collections.emptyList();
            }
            constraint = unifier.constraint();
        }
        constraint = constraint.simplify(context);
        if (constraint.isFalse()) {
            return Collections.emptyList();
        }

        List<ConjunctiveFormula> candidates = constraint.getDisjunctiveNormalForm().conjunctions().stream()
                .map(c -> c.addAndSimplify(constrainedTerm.constraint(), context))
                .filter(c -> !c.isFalse())
                .map(ConjunctiveFormula::resolveNonDeterministicLookups)
                .map(ConjunctiveFormula::getDisjunctiveNormalForm)
                .map(DisjunctiveFormula::conjunctions)
                .flatMap(List::stream)
                .map(c -> c.simplify(context))
                .filter(c -> !c.isFalse())
                .collect(Collectors.toList());

        List<Pair<ConjunctiveFormula, Boolean>> solutions = Lists.newArrayList();
        for (ConjunctiveFormula candidate : candidates) {
            variables = variables == null ? constrainedTerm.variableSet() : variables;
            candidate = candidate.orientSubstitution(variables);

            ConjunctiveFormula solution = candidate.addAndSimplify(constraint(), context);
            if (solution.isFalse()) {
                continue;
            }

            /* OPTIMIZATION: if no narrowing happens, the constraint remains unchanged;
             * thus, there is no need to check satisfiability or expand patterns */
            boolean isMatching = candidate.isMatching(variables);
            if (!isMatching && solution.checkUnsat()) {
                continue;
            }

            assert solution.disjunctions().isEmpty();
            solutions.add(Pair.of(solution, isMatching));
        }

        return solutions;
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
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }
}
