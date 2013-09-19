package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.krun.api.io.FileSystem;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;


/**
 * @author AndreiS
 */
public class ConstrainedTerm extends Term {

    private final Term term;
    private final SymbolicConstraint lookups;
    private final SymbolicConstraint constraint;
    private final TermContext context;

    public ConstrainedTerm(Term term, SymbolicConstraint lookups, SymbolicConstraint constraint, 
            TermContext context) {
        super(term.kind);
        this.term = term;
        this.lookups = lookups;
        this.constraint = constraint;
        this.context = context;
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
    /*
    public SymbolicConstraint match(ConstrainedTerm constrainedTerm, Definition definition) {
        SymbolicConstraint unificationConstraint = new SymbolicConstraint(definition);
        unificationConstraint.add(term, constrainedTerm.term);
        unificationConstraint.simplify();
        if (unificationConstraint.isFalse() || !unificationConstraint.isSubstitution()) {
            return null;
        }

        unificationConstraint.addAll(constrainedTerm.lookups);
        unificationConstraint.simplify();
        if (unificationConstraint.isFalse() || !unificationConstraint.isSubstitution()) {
            return null;
        }


    }
    */

    public SymbolicConstraint matchImplies(ConstrainedTerm constrainedTerm) {
        SymbolicConstraint unificationConstraint = new SymbolicConstraint(constrainedTerm.termContext());
        unificationConstraint.add(term, constrainedTerm.term);
        unificationConstraint.simplify();
        if (unificationConstraint.isFalse() || !unificationConstraint.isSubstitution()) {
            return null;
        }

        SymbolicConstraint implicationConstraint = new SymbolicConstraint(constrainedTerm.termContext());
        implicationConstraint.addAll(unificationConstraint);
        implicationConstraint.addAll(constrainedTerm.lookups);
        implicationConstraint.addAll(constrainedTerm.constraint);
        implicationConstraint.simplify();

        unificationConstraint.addAll(constraint);
        unificationConstraint.simplify();
        if (!unificationConstraint.implies(implicationConstraint)) {
            return null;
        }

        unificationConstraint.addAll(implicationConstraint);

        return unificationConstraint;
    }

    ///**
    // * Simplify map lookups.
    // */
    //public ConstrainedTerm simplifyLookups() {
    //    for (SymbolicConstraint.Equality equality : constraint.equalities())
    //}

    public Term term() {
        return term;
    }

    public Collection<SymbolicConstraint> unify(ConstrainedTerm constrainedTerm) {
        if (!term.kind.equals(constrainedTerm.term.kind)) {
            return Collections.emptyList();
        }

        SymbolicConstraint unificationConstraint = new SymbolicConstraint(constrainedTerm.termContext());
        unificationConstraint.add(term, constrainedTerm.term());
        unificationConstraint.simplify();
        if (unificationConstraint.isFalse()) {
            return Collections.emptyList();
        }

        Collection<SymbolicConstraint> constraints = new ArrayList<SymbolicConstraint>();
        for (SymbolicConstraint solution : unificationConstraint.getMultiConstraints()) {
            if (SymbolicConstraint.TruthValue.FALSE == solution.addAll(constrainedTerm.lookups)) continue;
            if (SymbolicConstraint.TruthValue.FALSE == solution.addAll(constrainedTerm.constraint)) continue;
            if (SymbolicConstraint.TruthValue.FALSE == solution.addAll(constraint)) continue;

            solution.simplify();
            if (solution.isFalse()) {
                continue;
            }

            if (solution.checkUnsat()) {
                continue;
            }

            constraints.add(solution);
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
        return term.equals(constrainedTerm.term) && lookups.equals(constrainedTerm.lookups)
               && constraint.equals(constrainedTerm.constraint);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + term.hashCode();
        hash = hash * Utils.HASH_PRIME + lookups.hashCode();
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
        visitor.visit(this);
    }

}
