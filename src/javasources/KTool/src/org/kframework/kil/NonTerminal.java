// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

/** A nonterminal in a {@link Production}. Also abused in some places as a sort identifier */
public class NonTerminal extends ProductionItem {

    private Sort sort2;

    public NonTerminal(Sort sort2) {
        super();
        this.sort2 = sort2;
    }

    public NonTerminal(NonTerminal sort) {
        super(sort);
        this.sort2 = sort.sort2;
    }

    public String getName() {
        return getSort2().getName();
    }

    public void setSort2(Sort sort2) {
        this.sort2 = sort2;
    }

    public Sort getSort2() {
        return sort2.isCellSort() ? Sort.BAG : sort2;
    }

    public Sort getRealSort2() {
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
        if (!(obj instanceof NonTerminal))
            return false;

        NonTerminal srt = (NonTerminal) obj;

        if (!sort2.equals(srt.sort2))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        return sort2.hashCode();
    }

    @Override
    public NonTerminal shallowCopy() {
        return new NonTerminal(this);
    }
}
