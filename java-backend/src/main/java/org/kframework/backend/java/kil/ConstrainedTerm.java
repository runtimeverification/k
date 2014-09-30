// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.TruthValue;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import com.google.common.base.Predicate;
import com.google.common.collect.Maps;


/**
 * A K term associated with symbolic constraints.
 *
 * @author AndreiS
 */
public class ConstrainedTerm extends JavaSymbolicObject {

    public static class Data {
        public final Term term;
        /**
         * Represents key lookups of builtin data-structures as a symbolic
         * constraint.
         */
        public final SymbolicConstraint.Data lookupsData;
        public final SymbolicConstraint.Data constraintData;
        public Data(Term term, SymbolicConstraint.Data lookups,
                SymbolicConstraint.Data constraint) {
            super();
            this.term = term;
            this.lookupsData = lookups;
            this.constraintData = constraint;
        }
        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((constraintData == null) ? 0 : constraintData.hashCode());
            result = prime * result + ((lookupsData == null) ? 0 : lookupsData.hashCode());
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
            if (constraintData == null) {
                if (other.constraintData != null)
                    return false;
            } else if (!constraintData.equals(other.constraintData))
                return false;
            if (lookupsData == null) {
                if (other.lookupsData != null)
                    return false;
            } else if (!lookupsData.equals(other.lookupsData))
                return false;
            if (term == null) {
                if (other.term != null)
                    return false;
            } else if (!term.equals(other.term))
                return false;
            return true;
        }


    }

    private Data data;

    private final TermContext context;

    private final SymbolicConstraint lookups;

    private final SymbolicConstraint constraint;

    public ConstrainedTerm(Data data, TermContext context) {
        this.data = data;
        this.context = context;
        this.lookups = new SymbolicConstraint(data.lookupsData, context);
        this.constraint = new SymbolicConstraint(data.constraintData, context);
    }

    public ConstrainedTerm(Term term, SymbolicConstraint lookups, SymbolicConstraint constraint,
            TermContext context) {
        this(new Data(term, lookups.data, constraint.data), context);
    }

    public ConstrainedTerm(Term term, SymbolicConstraint constraint, TermContext context) {
        this(term, new SymbolicConstraint(context), constraint, context);
    }

    public ConstrainedTerm(Term term, TermContext context) {
        this(term, new SymbolicConstraint(context), new SymbolicConstraint(context), context);
    }

    public TermContext termContext() {
        return context;
    }

    public SymbolicConstraint constraint() {
        return constraint;
    }

    public boolean implies(ConstrainedTerm constrainedTerm) {
        return matchImplies(constrainedTerm) != null;
    }

    public SymbolicConstraint lookups() {
        return lookups;
    }

    /**
     * Checks if this constrained term implies the given constrained term, assuming the variables
     * occurring only in the given constrained term (but not in this constrained term) are
     * existentially quantified.
     */
    public SymbolicConstraint matchImplies(ConstrainedTerm constrainedTerm) {
        SymbolicConstraint unificationConstraint = new SymbolicConstraint(constrainedTerm.termContext());
        unificationConstraint.addAll(constraint.substitution());
        unificationConstraint.add(data.term, constrainedTerm.data.term);
        unificationConstraint.simplify();
        if (unificationConstraint.isFalse()) {
            return null;
        }

        /* apply pattern folding */
        unificationConstraint.simplify(true);
        unificationConstraint.addAll(constrainedTerm.lookups);
        unificationConstraint.addAll(constrainedTerm.constraint);
        unificationConstraint.simplify(true);
        if (unificationConstraint.isFalse()) {
            return null;
        }

        unificationConstraint.expandPatternsAndSimplify(false);
        // TODO(AndreiS): figure out when a map unification provided more data
        unificationConstraint.expandPatternsAndSimplify(false);
        unificationConstraint.expandPatternsAndSimplify(false);
        unificationConstraint.expandPatternsAndSimplify(false);

        final Set<Variable> variables = unificationConstraint.variableSet();
        variables.removeAll(variableSet());
        unificationConstraint.orientSubstitution(variables);
        if (unificationConstraint.isFalse()
                || !unificationConstraint.substitution().keySet().containsAll(variables)) {
            return null;
        }

        SymbolicConstraint leftHandSide = SymbolicConstraint
                .simplifiedConstraintFrom(constrainedTerm.termContext(), constraint);

        Predicate<Variable> notInVariables = new Predicate<Variable>() {
            @Override
            public boolean apply(Variable var) {
                return variables.contains(var);
            }
        };
        SymbolicConstraint rightHandSide = SymbolicConstraint
                .simplifiedConstraintFrom(constrainedTerm.termContext(),
                        Maps.filterKeys(unificationConstraint.substitution(), notInVariables),
                        unificationConstraint.equalities(),
                        leftHandSide.substitution());

        if (!leftHandSide.implies(rightHandSide, variables)) {
            return null;
        }

        unificationConstraint.addAllThenSimplify(lookups, constraint);

        return unificationConstraint;
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
    public List<SymbolicConstraint> unify(ConstrainedTerm constrainedTerm) {
        /* unify the subject term and the pattern term without considering those associated constraints */
        SymbolicConstraint unificationConstraint = new SymbolicConstraint(constrainedTerm.termContext());
        unificationConstraint.add(data.term, constrainedTerm.data.term);
        unificationConstraint.simplify();
        if (unificationConstraint.isFalse()) {
            return Collections.emptyList();
        }

        List<SymbolicConstraint> solutions = new ArrayList<SymbolicConstraint>();
        for (SymbolicConstraint candidate : unificationConstraint.getMultiConstraints()) {
            if (TruthValue.FALSE ==
                    candidate.addAllThenSimplify(constrainedTerm.lookups, constrainedTerm.constraint)) {
                continue;
            }

            if (!candidate.isMatching(constrainedTerm.variableSet())) {
                if (TruthValue.FALSE == candidate.addAllThenSimplify(constraint)) {
                    continue;
                }

                if (candidate.checkUnsat()) {
                    continue;
                }

                // TODO(AndreiS): find a better place for pattern expansion
                candidate.expandPatternsAndSimplify(true);
            } else {
                SymbolicConstraint clonedConstraint = new SymbolicConstraint(constraint, context);
                clonedConstraint.addAll(candidate);
                candidate = clonedConstraint;
            }

            solutions.add(candidate);
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
        hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + data.hashCode();
        return hashCode;
    }

    @Override
    public String toString() {
        return data.term + SymbolicConstraint.SEPARATOR + constraint + SymbolicConstraint.SEPARATOR + lookups;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }
}
