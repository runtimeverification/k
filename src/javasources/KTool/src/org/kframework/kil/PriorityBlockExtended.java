// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

import java.util.ArrayList;
import java.util.List;

/** A group within a {@code syntax priorities} declaration.
 * @see PriorityExtended */
public class PriorityBlockExtended extends ASTNode implements Interfaces.MutableList<KLabelConstant, Enum<?>> {

    java.util.List<KLabelConstant> productions = new ArrayList<KLabelConstant>();

    public java.util.List<KLabelConstant> getProductions() {
        return productions;
    }

    public void setProductions(java.util.List<KLabelConstant> productions) {
        this.productions = productions;
    }

    public PriorityBlockExtended() {
        super();
    }

    public PriorityBlockExtended(PriorityBlockExtended node) {
        super(node);
        this.productions.addAll(node.productions);
    }

    public PriorityBlockExtended(java.util.List<KLabelConstant> productions) {
        super();
        this.productions.addAll(productions);
    }

    @Override
    public String toString() {
        String content = "";
        for (Term production : productions)
            content += production + " ";

        if (content.length() > 2)
            content = content.substring(0, content.length() - 1);

        return content;
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

        for (Term prd : productions)
            hash += prd.hashCode();
        return hash;
    }

    @Override
    public PriorityBlockExtended shallowCopy() {
        return new PriorityBlockExtended(this);
    }

    @Override
    public List<KLabelConstant> getChildren(Enum<?> _) {
        return productions;
    }

    @Override
    public void setChildren(List<KLabelConstant> children, Enum<?> _) {
        this.productions = children;
    }

}
