package org.kframework.backend.java.rewritemachine;

import java.util.List;
import java.util.Map;

import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;

class ExtendedSubstitution {

    private Map<Variable, Term> subst;
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