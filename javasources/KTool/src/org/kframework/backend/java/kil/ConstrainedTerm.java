package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;


/**
 * @author: AndreiS
 */
public class ConstrainedTerm extends Term {

    private final Term term;
    private final SymbolicConstraint lookups;
    private final SymbolicConstraint constraint;

    public ConstrainedTerm(Term term, SymbolicConstraint lookups, SymbolicConstraint constraint) {
        super(term.kind);
        this.term = term;
        this.lookups = lookups;
        this.constraint = constraint;
    }

    public ConstrainedTerm(Term term, SymbolicConstraint constraint, Context context) {
        this(term, new SymbolicConstraint(context), constraint);
    }

    public ConstrainedTerm(Term term, Context context) {
        this(term, new SymbolicConstraint(context), new SymbolicConstraint(context));
    }

    public SymbolicConstraint constraint() {
        return constraint;
    }
    public boolean implies(ConstrainedTerm constrainedTerm, Context context) {
        return match(constrainedTerm, context) != null;
    }

    public SymbolicConstraint match(ConstrainedTerm constrainedTerm, Context context) {
        SymbolicConstraint unificationConstraint = new SymbolicConstraint(context);
        unificationConstraint.add(term, constrainedTerm.term());
        unificationConstraint.simplify();
        if (unificationConstraint.isFalse() || !unificationConstraint.isSubstitution()) {
            return null;
        }

        unificationConstraint.addAll(constraint);
        unificationConstraint.simplify();

        if (!constraint.implies(constrainedTerm.constraint())) {
            return null;
        }
        unificationConstraint.addAll(constrainedTerm.constraint());

        return unificationConstraint;
    }

    /**
     * Simplify map lookups.
     */
    //public ConstrainedTerm simplifyLookups() {
    //    for (SymbolicConstraint.Equality equality : constraint.equalities())
    //}

    public Term term() {
        return term;
    }

    public Collection<SymbolicConstraint> unify(ConstrainedTerm constrainedTerm, Context context) {
        SymbolicConstraint unificationConstraint = new SymbolicConstraint(context);
        unificationConstraint.add(term, constrainedTerm.term());
        unificationConstraint.simplify();
        if (unificationConstraint.isFalse()) {
            return Collections.emptyList();
        }

        Collection<SymbolicConstraint> constraints = new ArrayList<SymbolicConstraint>();
        for (SymbolicConstraint constraint1 : unificationConstraint.getMultiConstraints()) {
            constraint1.addAll(constrainedTerm.lookups);
            constraint1.addAll(constrainedTerm.constraint);
            constraint1.addAll(constraint);

            constraint1.simplify();
            if (constraint1.isFalse()) {
                continue;
            }

            if (constraint1.checkUnsat()) {
                continue;
            }

            constraints.add(constraint1);
        }

        return constraints;
    }

    @Override
    public boolean isSymbolic() {
        throw new UnsupportedOperationException();
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
        return term.equals(constrainedTerm.term) && constraint.equals(constrainedTerm.constraint);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + term.hashCode();
        hash = hash * Utils.HASH_PRIME + constraint.hashCode();
        return hash;
    }

    @Override
    public String toString() {
        return term + SymbolicConstraint.SEPARATOR + constraint;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Visitor visitor) {
        throw new UnsupportedOperationException();
    }

}
