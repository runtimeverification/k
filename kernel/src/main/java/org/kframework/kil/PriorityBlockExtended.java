// Copyright (c) K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.definition.Tag;

import java.util.ArrayList;

/** A group within a {@code syntax priorities} declaration.
 * @see PriorityExtended */
public class PriorityBlockExtended extends ASTNode {

    java.util.List<Tag> productions = new ArrayList<>();

    public java.util.List<Tag> getProductions() {
        return productions;
    }

    public void setProductions(java.util.List<Tag> productions) {
        this.productions = productions;
    }

    public PriorityBlockExtended(java.util.List<Tag> productions) {
        super();
        this.productions.addAll(productions);
    }

    @Override
    public void toString(StringBuilder sb) {
        for (Tag production : productions) {
            sb.append(production);
            sb.append(" ");
        }
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (this == obj)
            return true;
        if (!(obj instanceof PriorityBlockExtended))
            return false;
        PriorityBlockExtended pb = (PriorityBlockExtended) obj;

        if (pb.productions.size() != productions.size())
            return false;

        for (int i = 0; i < pb.productions.size(); i++) {
            if (!pb.productions.get(i).equals(productions.get(i)))
                return false;
        }

        return true;
    }

    @Override
    public int hashCode() {
        int hash = 0;

        for (Tag prd : productions)
            hash += prd.hashCode();
        return hash;
    }

}
