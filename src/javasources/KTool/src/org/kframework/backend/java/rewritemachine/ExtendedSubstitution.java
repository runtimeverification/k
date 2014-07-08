// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.rewritemachine;

import java.util.List;
import java.util.Map;

import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

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
    private Map<Variable, Term> subst;
    
    /**
     * Contains references to the cells whose contents are going to be modified
     * by the rewrite rule; the references are collected as the rewrite machine
     * builds the substitution map.
     */
    private List<Cell<?>> writeCells;
    
    ExtendedSubstitution() {
        subst = Maps.newHashMap();
        writeCells = Lists.newArrayList();
    }
    
    ExtendedSubstitution(Map<Variable, Term> subst, List<Cell<?>> writeCells) {
        this.writeCells = writeCells;
        this.setSubst(subst);
    }

    Map<Variable, Term> substitution() {
        return subst;
    }

    void setSubst(Map<Variable, Term> subst) {
        this.subst = subst;
    }

    List<Cell<?>> writeCells() {
        return writeCells;
    }

    void addWriteCell(Cell<?> cell) {
        writeCells.add(cell);
    }
}