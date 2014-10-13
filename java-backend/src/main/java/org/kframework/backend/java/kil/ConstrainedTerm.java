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
import com.google.common.collect.Sets;


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
        public final SymbolicConstraint lookups;
        public final SymbolicConstraint constraint;
        public Data(Term term, SymbolicConstraint lookups,
                SymbolicConstraint constraint) {
            super();
            this.term = term;
            this.lookups = lookups;
            this.constraint = constraint;
        }
        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((constraint == null) ? 0 : constraint.hashCode());
            result = prime * result + ((lookups == null) ? 0 : lookups.hashCode());
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
            if (lookups == null) {
                if (other.lookups != null)
                    return false;
            } else if (!lookups.equals(other.lookups))
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

    public ConstrainedTerm(Term term, SymbolicConstraint lookups, SymbolicConstraint constraint) {
        Data data = new Data(term, lookups, constraint);
        this.data = data;
        this.context = data.constraint.termContext();
    }

    public ConstrainedTerm(Term term, SymbolicConstraint constraint) {
        this(term, new SymbolicConstraint(constraint.termContext()), constraint);
    }

    public ConstrainedTerm(Term term, TermContext context) {
        this(term, new SymbolicConstraint(context), new SymbolicConstraint(context));
    }

    public TermContext termContext() {
        return context;
    }

    public SymbolicConstraint constraint() {
        return data.constraint;
    }

    public SymbolicConstraint lookups() {
        return data.lookups;
    }

    public boolean implies(ConstrainedTerm constrainedTerm) {
        return matchImplies(constrainedTerm) != null;
    }

    /**
     * Checks if this constrained term implies the given constrained term, assuming the variables
     * occurring only in the given constrained term (but not in this constrained term) are
     * existentially quantified.
     */
    public SymbolicConstraint matchImplies(ConstrainedTerm constrainedTerm) {
        SymbolicConstraint unificationConstraint = new SymbolicConstraint(constrainedTerm.termContext());
        unificationConstraint.addAll(data.constraint.substitution());
        unificationConstraint.add(data.term, constrainedTerm.data.term);
        unificationConstraint.simplify();
        if (unificationConstraint.isFalse()) {
            return null;
        }

        /* apply pattern folding */
        unificationConstraint.simplifyModuloPatternFolding();
        unificationConstraint.addAll(constrainedTerm.data.lookups);
        unificationConstraint.addAll(constrainedTerm.data.constraint);
        unificationConstraint.simplifyModuloPatternFolding();
        if (unificationConstraint.isFalse()) {
            return null;
        }

        unificationConstraint.expandPatternsAndSimplify(false);
        // TODO(AndreiS): figure out when a map unification provided more data
        unificationConstraint.expandPatternsAndSimplify(false);
        unificationConstraint.expandPatternsAndSimplify(false);
        unificationConstraint.expandPatternsAndSimplify(false);

        final Set<Variable> variables = Sets.newHashSet(unificationConstraint.variableSet());
        variables.removeAll(variableSet());
        unificationConstraint.orientSubstitution(variables);
        if (unificationConstraint.isFalse()
                || !unificationConstraint.substitution().keySet().containsAll(variables)) {
            return null;
        }

        SymbolicConstraint leftHandSide = SymbolicConstraint
                .simplifiedConstraintFrom(constrainedTerm.termContext(), data.constraint);

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

        unificationConstraint.addAllThenSimplify(data.lookups, data.constraint);

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
                    candidate.addAllThenSimplify(constrainedTerm.data.lookups, constrainedTerm.data.constraint)) {
                continue;
            }

            if (!candidate.isMatching(constrainedTerm.variableSet())) {
                if (TruthValue.FALSE == candidate.addAllThenSimplify(data.constraint)) {
                    continue;
                }

                if (candidate.checkUnsat()) {
                    continue;
                }

                // TODO(AndreiS): find a better place for pattern expansion
                candidate.expandPatternsAndSimplify(true);
            } else {
                SymbolicConstraint clonedConstraint = new SymbolicConstraint(data.constraint);
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
        return data.term + SymbolicConstraint.SEPARATOR + data.constraint + SymbolicConstraint.SEPARATOR + data.lookups;
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
