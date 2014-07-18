// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Visitor;

import org.w3c.dom.Element;

/**
 * A subclass of {@link Empty} used to represent both typed and untyped cons list terminators. Distinguished by {@link #sort} and {@link #separator}
 */
public class ListTerminator extends Term {

    private final String separator; // Used only by toString()

    public ListTerminator(String sort, String separator) {
        super(sort);
        this.separator = separator;
    }

    public ListTerminator(String separator) {
        super(KSorts.K);
        this.separator = separator;
    }

    private ListTerminator(ListTerminator terminator) {
        super(terminator);
        this.separator = terminator.separator;
    }

    public ListTerminator(Element element, String separator) {
        super(element);
        this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
                this.separator = separator;
    }

    public String toString() {
        if (separator != null && sort.equals(KSorts.K)) {
            return ".List{\"" + separator + "\"}";
        } else {
        return "." + sort;
    }
        }

    @Override
    public ListTerminator shallowCopy() {
        return new ListTerminator(this);
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof ListTerminator))
            return false;
        ListTerminator l = (ListTerminator) o;
        return sort.equals(l.sort) && (separator == null && l.separator == null || separator != null && l.separator != null && separator.equals(l.separator));
    }

    @Override
    public int hashCode() {
        return (sort + separator).hashCode();
    }

    public String separator() {
        return this.separator;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
}
