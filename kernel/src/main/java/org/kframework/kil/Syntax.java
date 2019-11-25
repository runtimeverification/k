// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import com.beust.jcommander.internal.Lists;

import org.kframework.kore.Sort;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * A syntax declaration.
 * Contains {@link Production}s, grouped into a list {@link PriorityBlock}
 * according to precedence marked by {@code >} in the declaration.
 */
public class Syntax extends ModuleItem {
    /** The sort being declared. */
    NonTerminal sort;
    java.util.List<Sort> params;
    java.util.List<PriorityBlock> priorityBlocks;

    public Syntax(NonTerminal sort, List<Sort> params, List<PriorityBlock> priorities) {
        super();
        this.sort = sort;
        this.params = params;
        this.priorityBlocks = priorities;
    }

    public Syntax(NonTerminal sort, List<Sort> params) {
        this(sort, params, new ArrayList<PriorityBlock>());
    }

    /**
     * The sort being declared.
     */
    public NonTerminal getDeclaredSort() {
        return sort;
    }

    public List<Sort> getParams() {
        return params;
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
}
