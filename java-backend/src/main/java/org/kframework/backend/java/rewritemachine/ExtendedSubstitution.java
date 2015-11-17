// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.rewritemachine;

import java.util.List;

import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;

import com.google.common.collect.Lists;
import org.kframework.backend.java.symbolic.ImmutableMapSubstitution;
import org.kframework.backend.java.symbolic.Substitution;

/**
 * Represents a substitution map plus extra information used by
 * {@link KAbstractRewriteMachine}.
 *
 * @author YilongL
 *
 */
class ExtendedSubstitution {

    /**
     * Represents the substitution map obtained by matching a pattern against
     * (part of) the subject term.
     */
    private Substitution<Variable, Term> subst;

    /**
     * Contains references to the cells whose contents are going to be modified
     * by the rewrite rule; the references are collected as the rewrite machine
     * builds the substitution map.
     */
    private final List<CellCollection.Cell> writeCells;

    ExtendedSubstitution() {
        subst = ImmutableMapSubstitution.empty();
        writeCells = Lists.newArrayList();
    }

    ExtendedSubstitution(Substitution<Variable, Term> subst, List<CellCollection.Cell> writeCells) {
        this.writeCells = writeCells;
        this.setSubst(subst);
    }

    Substitution<Variable, Term> substitution() {
        return subst;
    }

    void setSubst(Substitution<Variable, Term> subst) {
        this.subst = subst;
    }

    List<CellCollection.Cell> writeCells() {
        return writeCells;
    }

    void addWriteCell(CellCollection.Cell cell) {
        writeCells.add(cell);
    }

    @Override
    public String toString() {
        return "extSubst(" + subst + ", " + writeCells + ")";
    }
}