// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

/** A priority declaration, {@code syntax priorities} <em>labels</em> {@code >} ... {@code >} <em>labels</em>.
 * @see PriorityBlockExtended
 */
public class PriorityExtended extends ModuleItem {
    /** Highest priority block comes first */
    java.util.List<PriorityBlockExtended> priorityBlocks;

    public PriorityExtended(java.util.List<PriorityBlockExtended> priorities) {
        super();
        this.priorityBlocks = priorities;
    }

    public java.util.List<PriorityBlockExtended> getPriorityBlocks() {
        return priorityBlocks;
    }

    @Override
    public void toString(StringBuilder sb) {
        sb.append("  syntax priorities ");
        String conn = "";
        for (PriorityBlockExtended pb : priorityBlocks) {
            sb.append(conn);
            pb.toString(sb);
            conn = " > ";
        }
        sb.append(" ");
        sb.append(getAttributes());
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

}
