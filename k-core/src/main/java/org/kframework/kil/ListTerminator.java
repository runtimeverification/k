// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.StringUtil;

import org.w3c.dom.Element;

/**
 * A subclass of {@link ListTerminator} used to represent both typed and untyped cons list terminators. Distinguished by {@link #sort} and {@link #separator}
 */
public class ListTerminator extends Term {

    private final String separator; // Used only by toString()
    private final boolean userTyped;

    public ListTerminator(Sort sort, String separator) {
        super(sort);
        this.separator = separator;
        userTyped = true;
    }

    public ListTerminator(String separator) {
        super(Sort.K);
        this.separator = separator;
        userTyped = true;
    }

    private ListTerminator(ListTerminator terminator) {
        super(terminator);
        this.separator = terminator.separator;
        this.userTyped = terminator.userTyped;
    }

    public ListTerminator(Element element, String separator) {
        super(element);
        this.sort = Sort.of(element.getAttribute(Constants.SORT_sort_ATTR));
        this.userTyped = Boolean.parseBoolean(element.getAttribute(Constants.TYPE_userTyped_ATTR));
        this.separator = separator;
    }

    @Override
    public String toString() {
        if (separator != null && sort.equals(Sort.K)) {
            return ".List{" + StringUtil.enquoteKString(separator) + "}";
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

    public boolean isUserTyped() {
        return userTyped;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
}
