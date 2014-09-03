// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.rewritemachine.Instruction;
import org.kframework.kil.BuiltinLookup;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;

public class JavaBackendRuleData {
    private List<BuiltinLookup> lookups;
    private Map<Variable, Integer> concreteDataStructureSize;
    private boolean compiledForFastRewriting;
    private ImmutableSet<String> cellsOfInterest;
    private Map<String, Term> lhsOfReadCell;
    private Map<String, Term> rhsOfWriteCell;
    private ImmutableSet<String> cellsToCopy;
    private ImmutableList<Instruction> instructions;

    public JavaBackendRuleData(List<BuiltinLookup> lookups,
            Map<Variable, Integer> concreteDataStructureSize,
            boolean compiledForFastRewriting) {
        this.lookups = lookups;
        this.concreteDataStructureSize = concreteDataStructureSize;
        this.compiledForFastRewriting = compiledForFastRewriting;
    }

    public List<BuiltinLookup> getLookups() {
        return lookups;
    }

    public void setLookups(List<BuiltinLookup> lookups) {
        this.lookups = lookups;
    }

    public Map<Variable, Integer> getConcreteDataStructureSize() {
        return concreteDataStructureSize;
    }

    public void setConcreteDataStructureSize(Map<Variable, Integer> concreteDataStructureSize) {
        this.concreteDataStructureSize = concreteDataStructureSize;
    }

    public boolean isCompiledForFastRewriting() {
        return compiledForFastRewriting;
    }

    public void setCompiledForFastRewriting(boolean compiledForFastRewriting) {
        this.compiledForFastRewriting = compiledForFastRewriting;
    }

    public Set<String> getCellsOfInterest() {
        return cellsOfInterest;
    }

    public void setCellsOfInterest(Set<String> cellsOfInterest) {
        this.cellsOfInterest = ImmutableSet.copyOf(cellsOfInterest);
    }

    public Set<String> getReadCells() {
        return lhsOfReadCell.keySet();
    }

    public Set<String> getWriteCells() {
        return rhsOfWriteCell.keySet();
    }

    public Map<String, Term> getLhsOfReadCell() {
        return Collections.unmodifiableMap(lhsOfReadCell);
    }

    public void setLhsOfReadCell(Map<String, Term> lhsOfReadCell) {
        // unable to use Guava's ImmutableMap because of possible null values
        this.lhsOfReadCell = Maps.newHashMap(lhsOfReadCell);
    }

    public Map<String, Term> getRhsOfWriteCell() {
        return Collections.unmodifiableMap(rhsOfWriteCell);
    }

    public void setRhsOfWriteCell(Map<String, Term> rhsOfWriteCell) {
        // unable to use Guava's ImmutableMap because of possible null values
        this.rhsOfWriteCell = Maps.newHashMap(rhsOfWriteCell);
    }

    public List<Instruction> getInstructions() {
        return instructions;
    }

    public void setInstructions(List<Instruction> instructions) {
        this.instructions = ImmutableList.copyOf(instructions);
    }

    public void setCellsToCopy(Set<String> cellsToCopy) {
        this.cellsToCopy = ImmutableSet.copyOf(cellsToCopy);
    }

    public Set<String> getCellsToCopy() {
        return cellsToCopy;
    }
}
