// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.List;

import org.kframework.kil.visitors.Visitor;

/** A priority declaration, {@code syntax priorities} <em>labels</em> {@code >} ... {@code >} <em>labels</em>.
 * @see PriorityBlockExtended
 */
public class PriorityExtended extends ModuleItem  implements Interfaces.MutableList<PriorityBlockExtended, Enum<?>>{
    /** Highest priority block comes first */
    java.util.List<PriorityBlockExtended> priorityBlocks;

    public PriorityExtended(java.util.List<PriorityBlockExtended> priorities) {
        super();
        this.priorityBlocks = priorities;
    }

    public java.util.List<PriorityBlockExtended> getPriorityBlocks() {
        return priorityBlocks;
    }

    public void setPriorityBlocks(java.util.List<PriorityBlockExtended> priorityBlocks) {
        this.priorityBlocks = priorityBlocks;
    }

    public PriorityExtended(PriorityExtended node) {
        super(node);
        this.priorityBlocks = node.priorityBlocks;
    }

    @Override
    public String toString() {
        String blocks = "";

        for (PriorityBlockExtended pb : priorityBlocks) {
            blocks += pb + "\n> ";
        }
        if (blocks.length() > 2)
            blocks = blocks.substring(0, blocks.length() - 3);

        return "  syntax priorities" + blocks + "\n";
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
        if (!(obj instanceof PriorityExtended))
            return false;
        PriorityExtended syn = (PriorityExtended) obj;

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
        int hash = 0;

        for (PriorityBlockExtended pb : priorityBlocks)
            hash += pb.hashCode();
        return hash;
    }

    @Override
    public PriorityExtended shallowCopy() {
        return new PriorityExtended(this);
    }

    @Override
    public List<PriorityBlockExtended> getChildren(Enum<?> _) {
        return priorityBlocks;
    }
    
    @Override
    public void setChildren(List<PriorityBlockExtended> children, Enum<?> _) {
        this.priorityBlocks = children;
    }
}
