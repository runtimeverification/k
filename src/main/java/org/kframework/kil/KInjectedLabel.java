// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

/** Represents a term of sort KLabel made by injecting something else.
 * Corresponds to operators Foo2KLabel and #_ in source.
 * Usually only occurs as the label of a {@link KApp} an {@link Empty} as arguments.
 */
public class KInjectedLabel extends Term implements Interfaces.MutableParent<Term, Enum<?>> {
    protected Term term;

    public KInjectedLabel(Location location, Source source) {
        super(location, source, Sort.KLABEL);
    }

    public KInjectedLabel(KInjectedLabel l) {
        super(l);
        term = l.term;
    }

    public KInjectedLabel(Term t) {
        super(Sort.KLABEL);
        term = t;
    }

    public Term getTerm() {
        return term;
    }

    public void setTerm(Term term) {
        this.term = term;
    }

    @Override
    public String toString() {
        return "# " + term;
    }

    public static Sort getInjectedSort(Sort sort) {
        if (sort.equals(Sort.BAG_ITEM))
            return Sort.BAG;
        if (sort.equals(Sort.SET_ITEM))
            return Sort.SET;
        if (sort.equals(Sort.MAP_ITEM))
            return Sort.MAP;
        if (sort.equals(Sort.LIST_ITEM))
            return Sort.LIST;
        return sort;
    }

    @Override
    public KInjectedLabel shallowCopy() {
        return new KInjectedLabel(this);
    }

    @Override
    public boolean equals(Object o) {
        if (getClass() != o.getClass()) return false;
        KInjectedLabel k = (KInjectedLabel)o;
        return term.equals(k.term);
    }

    @Override
    public boolean contains(Object o) {
        if (o instanceof Bracket)
            return contains(((Bracket)o).getContent());
        if (o instanceof Cast)
            return contains(((Cast)o).getContent());
        if (getClass() != o.getClass()) return false;
        KInjectedLabel k = (KInjectedLabel)o;
        return term.contains(k.term);
    }

    @Override
    public int hashCode() {
        return term.hashCode();
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public Term getChild(Enum<?> type) {
        return term;
    }

    @Override
    public void setChild(Term child, Enum<?> type) {
        this.term = child;
    }
}
