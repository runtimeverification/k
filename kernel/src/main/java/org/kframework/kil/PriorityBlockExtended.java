// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.definition.Tag;

import java.util.ArrayList;
import java.util.List;

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

    public PriorityBlockExtended(PriorityBlockExtended node) {
        super(node);
        this.productions.addAll(node.productions);
    }

    public PriorityBlockExtended(java.util.List<Tag> productions) {
        super();
        this.productions.addAll(productions);
    }

    @Override
    public String toString() {
        String content = "";
        for (Tag production : productions)
            content += production + " ";

        if (content.length() > 2)
            content = content.substring(0, content.length() - 1);

        return content;
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

    @Override
    public PriorityBlockExtended shallowCopy() {
        return new PriorityBlockExtended(this);
    }
}
