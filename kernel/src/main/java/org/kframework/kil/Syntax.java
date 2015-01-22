// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

import com.beust.jcommander.internal.Lists;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * A syntax declaration.
 * Contains {@link Production}s, grouped into a list {@link PriorityBlock}
 * according to precedence marked by {@code >} in the declaration.
 */
public class Syntax extends ModuleItem implements Interfaces.MutableParent<NonTerminal, Enum<?>>,
        Interfaces.MutableList<PriorityBlock, Enum<?>> {
    /** The sort being declared. */
    NonTerminal sort;
    java.util.List<PriorityBlock> priorityBlocks;

    public Syntax(NonTerminal sort, java.util.List<PriorityBlock> priorities) {
        super();
        this.sort = sort;
        this.priorityBlocks = priorities;
    }

    public Syntax(NonTerminal sort, PriorityBlock... priorities) {
        this(sort, Lists.newArrayList(priorities));
    }

    public Syntax(NonTerminal sort) {
        this(sort, new ArrayList<PriorityBlock>());
    }

    /**
     * The sort being declared.
     */
    public NonTerminal getDeclaredSort() {
        return sort;
    }

    public void setSort(NonTerminal sort) {
        this.sort = sort;
    }

    public java.util.List<PriorityBlock> getPriorityBlocks() {
        return priorityBlocks;
    }

    public void setPriorityBlocks(java.util.List<PriorityBlock> priorityBlocks) {
        this.priorityBlocks = priorityBlocks;
    }

    public Syntax(Syntax node) {
        super(node);
        this.sort = node.sort;
        this.priorityBlocks = node.priorityBlocks;
    }

    @Override
    public String toString() {
        String blocks = "";

        for (PriorityBlock pb : priorityBlocks) {
            blocks += pb + "\n> ";
        }
        if (blocks.length() > 2)
            blocks = blocks.substring(0, blocks.length() - 3);

        return "  syntax " + sort + " ::= " + blocks + "\n";
    }

    @Override
    public List<String> getLabels() {
        List<String> lbls = new LinkedList<String>();
        for (PriorityBlock pb : priorityBlocks) {
            for (Production prod : pb.getProductions()) {
                lbls.add(prod.getLabel());
            }
        }
        return lbls;
    }

    @Override
    public List<String> getKLabels() {
        List<String> lbls = new LinkedList<String>();
        if (priorityBlocks == null)
            return lbls;
        for (PriorityBlock pb : priorityBlocks) {
            for (Production prod : pb.getProductions()) {
                if (prod.getSort().isComputationSort() || prod.getSort().equals(Sort.KLABEL) && prod.isConstant()) {
                    lbls.add(prod.getKLabelOfKItem());
                }
            }
        }
        return lbls;
    }

    @Override
    public List<Sort> getAllSorts() {
        List<Sort> sorts = new ArrayList<>();
        sorts.add(sort.getSort());
        return sorts;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (this == obj)
            return true;
        if (!(obj instanceof Syntax))
            return false;
        Syntax syn = (Syntax) obj;

        if (!syn.getDeclaredSort().equals(this.sort))
            return false;

        if (syn.priorityBlocks.size() != priorityBlocks.size())
            return false;

        for (int i = 0; i < syn.priorityBlocks.size(); i++) {
            if (!syn.priorityBlocks.get(i).equals(priorityBlocks.get(i)))
                return false;
        }

        return true;
    }

    @Override
    public int hashCode() {
        int hash = sort.hashCode();

        for (PriorityBlock pb : priorityBlocks)
            hash += pb.hashCode();
        return hash;
    }

    @Override
    public Syntax shallowCopy() {
        return new Syntax(this);
    }

    @Override
    public NonTerminal getChild(Enum<?> type) {
        return sort;
    }

    @Override
    public List<PriorityBlock> getChildren(Enum<?> type) {
        return priorityBlocks;
    }

    @Override
    public void setChildren(List<PriorityBlock> children, Enum<?> cls) {
        this.priorityBlocks = children;
    }

    @Override
    public void setChild(NonTerminal child, Enum<?> type) {
        this.sort = child;
    }
}
