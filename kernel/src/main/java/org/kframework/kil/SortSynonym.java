// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kore.Sort;

public class SortSynonym extends ModuleItem {

    public final Sort newSort;
    public final Sort oldSort;

    public SortSynonym(NonTerminal newSort, NonTerminal oldSort) {
        super();
        this.newSort = newSort.getSort();
        this.oldSort = oldSort.getSort();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        SortSynonym other = (SortSynonym) obj;
        if (!newSort.equals(other.newSort))
            return false;
        if (!oldSort.equals(other.oldSort))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + newSort.hashCode();
        result = prime * result + oldSort.hashCode();
        return result;
    }

    @Override
    public void toString(StringBuilder sb) {
      sb.append("  syntax ").append(newSort).append(" = ").append(oldSort).append(" ").append(getAttributes());
    }

}
