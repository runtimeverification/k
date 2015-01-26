// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.kil.ASTNode;

import java.util.Collection;

/**
 * A disjunction of conjunctions.
 *
 * @see org.kframework.backend.java.symbolic.ConjunctiveFormula
 */
public class DisjunctiveFormula extends Term {

    private final PersistentUniqueList<ConjunctiveFormula> conjunctions;

    public DisjunctiveFormula(Collection<ConjunctiveFormula> conjunctions) {
        super(Kind.KITEM);
        this.conjunctions = conjunctions instanceof PersistentUniqueList ?
                (PersistentUniqueList<ConjunctiveFormula>) conjunctions :
                PersistentUniqueList.<ConjunctiveFormula>empty().plusAll(conjunctions);
    }

    public PersistentUniqueList<ConjunctiveFormula> conjunctions() {
        return conjunctions;
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public boolean isSymbolic() {
        return true;
    }

    @Override
    public Sort sort() {
        return Sort.BOOL;
    }

    @Override
    protected boolean computeMutability() {
        return false;
    }

    @Override
    protected int computeHash() {
        return conjunctions.hashCode();
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof DisjunctiveFormula)) {
            return false;
        }

        DisjunctiveFormula disjunction = (DisjunctiveFormula) object;
        return conjunctions.equals(disjunction.conjunctions);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {

    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return null;
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {

    }

    @Override
    public void accept(Visitor visitor) {

    }
}
