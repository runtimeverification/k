// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

/** A nonterminal in a {@link Production}. Also abused in some places as a sort identifier */
public class Sort extends ProductionItem {

    private Sort2 sort2;

    public Sort(Sort2 sort2) {
        super();
        this.sort2 = sort2;
    }

    public Sort(Sort sort) {
        super(sort);
        this.sort2 = sort.sort2;
    }

    public String getName() {
        return getSort2().getName();
    }

    public void setSort2(Sort2 sort2) {
        this.sort2 = sort2;
    }

    public Sort2 getSort2() {
        return sort2.isCellSort() ? Sort2.BAG : sort2;
    }

    public Sort2 getRealSort2() {
        return sort2;
    }

    @Override
    public String toString() {
        return sort2.getName();
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (obj == this)
            return true;
        if (!(obj instanceof Sort))
            return false;

        Sort srt = (Sort) obj;

        if (!sort2.equals(srt.sort2))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        return sort2.hashCode();
    }

    @Override
    public Sort shallowCopy() {
        return new Sort(this);
    }
}
