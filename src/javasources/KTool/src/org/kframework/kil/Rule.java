// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.rewritemachine.Instruction;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;


/**
 * A rule declaration.
 * The left and right hand sides of the rewrite are described by the single term
 * {@code body} which allows {@link Rewrite} nodes to describe the changes.
 * Any explicit attributes on the rule are stored in {@link #attributes}.
 */
public class Rule extends Sentence {

    private List<BuiltinLookup> lookups = Collections.emptyList();
    private Map<Variable, Integer> concreteDataStructureSize = Collections.emptyMap();

    private boolean compiledForFastRewriting = false;
    // TODO(YilongL): maybe build a CellInfo class?
    private Set<String> cellsOfInterest;
    private Map<String, Term> lhsOfReadCell;
    private Map<String, Term> rhsOfWriteCell;
    private Set<String> cellsToCopy;
    private List<Instruction> instructions;

    public Rule(Element element) {
        super(element);
    }

    public Rule(Rule node) {
        super(node);
        lookups = node.lookups;
        concreteDataStructureSize = node.concreteDataStructureSize;

        compiledForFastRewriting = node.compiledForFastRewriting;
        cellsOfInterest = node.cellsOfInterest;
        lhsOfReadCell = node.lhsOfReadCell;
        rhsOfWriteCell = node.rhsOfWriteCell;
        cellsToCopy = node.cellsToCopy;
        instructions = node.instructions;
    }

    public Rule() {
        super();
    }

    public Rule(Term lhs, Term rhs, Context context) {
        super();
        this.setBody(new Rewrite(lhs, rhs, context));
    }

    public Rule(Term lhs, Term rhs, Term requires, Term ensures, Context context) {
        this(lhs, rhs, context);
        this.setRequires(requires);
        this.setEnsures(ensures);
    }

    public Rule(Sentence term) {
        super(term);
    }

    public String toString() {
        String content = "  rule ";

        if (this.label != null && !this.label.equals(""))
            content += "[" + this.label + "]: ";

        content += this.body + " ";
        if (this.requires != null) {
            content += "requires " + this.requires + " ";
        }
        if (this.ensures != null) {
            content += "ensures " + this.ensures + " ";
        }

        return content + attributes;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public Rule shallowCopy() {
        return new Rule(this);
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
