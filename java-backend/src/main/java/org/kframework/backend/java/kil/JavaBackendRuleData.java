// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.io.Serializable;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.collections4.map.UnmodifiableMap;
import org.kframework.backend.java.rewritemachine.MatchingInstruction;
import org.kframework.kil.BuiltinLookup;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;

public class JavaBackendRuleData implements Serializable {
    private final ImmutableList<BuiltinLookup> lookups;
    private final ImmutableMap<Variable, Integer> concreteDataStructureSize;
    private final boolean compiledForFastRewriting;
    private final ImmutableSet<String> cellsOfInterest;
    // unable to use Guava's ImmutableMap because of possible null values
    private final UnmodifiableMap<String, Term> lhsOfReadCell;
    private final UnmodifiableMap<String, Term> rhsOfWriteCell;
    private final ImmutableSet<String> cellsToCopy;
    private final ImmutableList<MatchingInstruction> instructions;

    public JavaBackendRuleData(ImmutableList<BuiltinLookup> lookups,
            ImmutableMap<Variable, Integer> concreteDataStructureSize,
            boolean compiledForFastRewriting,
            ImmutableSet<String> cellsOfInterest,
            UnmodifiableMap<String, Term> lhsOfReadCell,
            UnmodifiableMap<String, Term> rhsOfWriteCell,
            ImmutableSet<String> cellsToCopy,
            ImmutableList<MatchingInstruction> instructions) {
        super();
        this.lookups = lookups;
        this.concreteDataStructureSize = concreteDataStructureSize;
        this.compiledForFastRewriting = compiledForFastRewriting;
        this.cellsOfInterest = cellsOfInterest;
        this.lhsOfReadCell = lhsOfReadCell;
        this.rhsOfWriteCell = rhsOfWriteCell;
        this.cellsToCopy = cellsToCopy;
        this.instructions = instructions;
    }


    public JavaBackendRuleData() {
        super();
        lookups = ImmutableList.of();
        concreteDataStructureSize = ImmutableMap.of();
        compiledForFastRewriting = false;
        cellsOfInterest = null;
        lhsOfReadCell = null;
        rhsOfWriteCell = null;
        cellsToCopy = null;
        instructions = null;
    }


    public List<BuiltinLookup> getLookups() {
        return lookups;
    }

    public JavaBackendRuleData setLookups(List<BuiltinLookup> lookups2) {
        JavaBackendRuleData ruleData = new JavaBackendRuleData(
                ImmutableList.copyOf(lookups2), concreteDataStructureSize, compiledForFastRewriting, cellsOfInterest,
                lhsOfReadCell, rhsOfWriteCell, cellsToCopy, instructions);
        return ruleData;
    }

    public Map<Variable, Integer> getConcreteDataStructureSize() {
        return concreteDataStructureSize;
    }

    public JavaBackendRuleData setConcreteDataStructureSize(Map<Variable, Integer> concreteDataStructureSize2) {
        JavaBackendRuleData ruleData = new JavaBackendRuleData(
                lookups, ImmutableMap.copyOf(concreteDataStructureSize2), compiledForFastRewriting, cellsOfInterest,
                lhsOfReadCell, rhsOfWriteCell, cellsToCopy, instructions);
        return ruleData;
    }

    public boolean isCompiledForFastRewriting() {
        return compiledForFastRewriting;
    }

    public JavaBackendRuleData setCompiledForFastRewriting(boolean compiledForFastRewriting2) {
        JavaBackendRuleData ruleData = new JavaBackendRuleData(
                lookups, concreteDataStructureSize, compiledForFastRewriting2, cellsOfInterest,
                lhsOfReadCell, rhsOfWriteCell, cellsToCopy, instructions);
        return ruleData;
    }

    public Set<String> getCellsOfInterest() {
        return cellsOfInterest;
    }

    public JavaBackendRuleData setCellsOfInterest(Set<String> cellsOfInterest2) {
        JavaBackendRuleData ruleData = new JavaBackendRuleData(
                lookups, concreteDataStructureSize, compiledForFastRewriting, ImmutableSet.copyOf(cellsOfInterest2),
                lhsOfReadCell, rhsOfWriteCell, cellsToCopy, instructions);
        return ruleData;
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

    public JavaBackendRuleData setLhsOfReadCell(Map<String, Term> lhsOfReadCell2) {
        JavaBackendRuleData ruleData = new JavaBackendRuleData(
                lookups, concreteDataStructureSize, compiledForFastRewriting, cellsOfInterest,
                (UnmodifiableMap<String, Term>) UnmodifiableMap.unmodifiableMap(Maps.newHashMap(lhsOfReadCell2)),
                rhsOfWriteCell, cellsToCopy, instructions);
        return ruleData;
    }

    public Map<String, Term> getRhsOfWriteCell() {
        return Collections.unmodifiableMap(rhsOfWriteCell);
    }

    public JavaBackendRuleData setRhsOfWriteCell(Map<String, Term> rhsOfWriteCell2) {
        JavaBackendRuleData ruleData = new JavaBackendRuleData(
                lookups, concreteDataStructureSize, compiledForFastRewriting, cellsOfInterest,
                lhsOfReadCell, (UnmodifiableMap<String, Term>) UnmodifiableMap.unmodifiableMap(Maps.newHashMap(rhsOfWriteCell2)),
                cellsToCopy, instructions);
        return ruleData;
    }

    public List<MatchingInstruction> getMatchingInstructions() {
        return instructions;
    }

    public JavaBackendRuleData setInstructions(List<MatchingInstruction> instructions2) {
        JavaBackendRuleData ruleData = new JavaBackendRuleData(
                lookups, concreteDataStructureSize, compiledForFastRewriting, cellsOfInterest,
                lhsOfReadCell, rhsOfWriteCell, cellsToCopy, ImmutableList.copyOf(instructions2));
        return ruleData;
    }

    public Set<String> getCellsToCopy() {
        return cellsToCopy;
    }

    public JavaBackendRuleData setCellsToCopy(Set<String> cellsToCopy2) {
        JavaBackendRuleData ruleData = new JavaBackendRuleData(
                lookups, concreteDataStructureSize, compiledForFastRewriting, cellsOfInterest,
                lhsOfReadCell, rhsOfWriteCell, ImmutableSet.copyOf(cellsToCopy2), instructions);
        return ruleData;
    }
}
