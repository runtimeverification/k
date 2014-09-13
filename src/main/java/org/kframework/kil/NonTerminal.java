// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

/** A nonterminal in a {@link Production}. Also abused in some places as a sort identifier */
public class NonTerminal extends ProductionItem {

    private Sort sort;

    public NonTerminal(Sort sort) {
        super();
        this.sort = sort;
    }

    public NonTerminal(NonTerminal nonTerminal) {
        super(nonTerminal);
        this.sort = nonTerminal.sort;
    }

    public String getName() {
        return getSort().getName();
    }

    public void setSort(Sort sort) {
        this.sort = sort;
    }

    public Sort getSort() {
        return sort.isCellSort() ? Sort.BAG : sort;
    }

    public Sort getRealSort() {
        return sort;
    }

    @Override
    public String toString() {
        return sort.getName();
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

        NonTerminal nt = (NonTerminal) obj;

        if (!sort.equals(nt.sort))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        return sort.hashCode();
    }

    @Override
    public NonTerminal shallowCopy() {
        return new NonTerminal(this);
    }
}
