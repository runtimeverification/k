// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

/** Represents a term of sort KLabel made by injecting something else.
 * Corresponds to operators Foo2KLabel and #_ in source.
 * Usually only occurs as the label of a {@link KApp} an {@link Empty} as arguments.
 */
public class KInjectedLabel extends Term implements Interfaces.MutableParent<Term, Enum<?>> {
    protected Term term;

    public KInjectedLabel(String location, String filename) {
        super(location, filename, KSorts.KLABEL);
    }

    public KInjectedLabel(KInjectedLabel l) {
        super(l);
        term = l.term;
    }

    public KInjectedLabel(Term t) {
        super(KSorts.KLABEL);
        term = t;
    }

    public Term getTerm() {
        return term;
    }

    public void setTerm(Term term) {
        this.term = term;
    }

    public String toString() {
        return "# " + term;
    }

    public static String getInjectedSort(String sort) {
        if (sort.equals("BagItem"))
            return "Bag";
        if (sort.equals("SetItem"))
            return "Set";
        if (sort.equals("MapItem"))
            return "Map";
        if (sort.equals("ListItem"))
            return "List";
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
