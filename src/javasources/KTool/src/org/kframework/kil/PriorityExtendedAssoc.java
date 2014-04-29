// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.List;

import org.kframework.kil.visitors.Visitor;

/**
 * An associativity declaration, one of {@code syntax left}, {@code syntax right}, or {@ code syntax non-assoc}.
 */
public class PriorityExtendedAssoc extends ModuleItem implements Interfaces.MutableList<KLabelConstant, Enum<?>>{
    /** "left", "right", "non-assoc" */
    String assoc = null;
    /** The labels getting an associativity. */
    java.util.List<KLabelConstant> tags;

    public String getAssoc() {
        return assoc;
    }

    public void setAssoc(String assoc) {
        this.assoc = assoc;
    }

    public java.util.List<KLabelConstant> getTags() {
        return tags;
    }

    public void setTags(java.util.List<KLabelConstant> tags) {
        this.tags = tags;
    }

    public PriorityExtendedAssoc(String assoc, java.util.List<KLabelConstant> tags) {
        super();
        this.tags = tags;
        this.assoc = assoc;
    }

    public PriorityExtendedAssoc(PriorityExtendedAssoc node) {
        super(node);
        this.assoc = node.assoc;
        this.tags = node.tags;
    }

    @Override
    public String toString() {
        String blocks = "";

        for (KLabelConstant pb : tags) {
            blocks += pb + " ";
        }
        if (blocks.length() > 2)
            blocks = blocks.substring(0, blocks.length() - 1);

        return "  syntax " + assoc + " " + blocks + "\n";
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
        if (!(obj instanceof PriorityExtendedAssoc))
            return false;
        PriorityExtendedAssoc syn = (PriorityExtendedAssoc) obj;

        if (syn.tags.size() != tags.size())
            return false;

        for (int i = 0; i < syn.tags.size(); i++) {
            if (!syn.tags.get(i).equals(tags.get(i)))
                return false;
        }

        return true;
    }

    @Override
    public int hashCode() {
        int hash = assoc.hashCode();

        for (KLabelConstant pb : tags)
            hash += pb.hashCode();
        return hash;
    }

    @Override
    public PriorityExtendedAssoc shallowCopy() {
        return new PriorityExtendedAssoc(this);
    }

    @Override
    public List<KLabelConstant> getChildren(Enum<?> _) {
        return tags;
    }
    
    @Override
    public void setChildren(List<KLabelConstant> children, Enum<?> _) {
        this.tags = children;
    }
}
