// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.*;
import org.kframework.kil.loader.Context;
import org.kframework.utils.StringUtil;
import org.w3c.dom.Element;

/**
 * Abstract class representing a {@link KLabel} of the form #token("SORT", "VALUE").
 */
public abstract class Token extends KLabel {

    /**
     * Returns a {@link Token} of the given sort with the given value. The {@link Token} object is an instance of {@link BoolBuiltin}, {@link IntBuiltin},
     * {@link StringBuiltin}, or {@link GenericToken}.
     *
     * @param sort
     * @param value
     * @return
     */
    public static Token of(Sort sort, String value) {
        if (sort.equals(Sort.BUILTIN_BOOL)) {
            return BoolBuiltin.of(value);
        } else if (sort.equals(Sort.BUILTIN_INT)) {
            return IntBuiltin.of(value);
        } else if (sort.equals(Sort.BUILTIN_FLOAT)) {
            return FloatBuiltin.of(value);
        } else if (sort.equals(Sort.BUILTIN_STRING)) {
            /* TODO(andreis): unescape string */
            return StringBuiltin.of(value);
        } else {
            return GenericToken.of(sort, value);
        }
    }

    /**
     * Returns a {@link KApp} representing a {@link Token} of the given sort with the given value applied to an empty {@link KList}.
     *
     * @param sort
     * @param value
     * @return
     */
    public static KApp kAppOf(Sort sort, String value) {
        if (sort.equals(Sort.BUILTIN_BOOL) || sort.equals(Sort.BOOL)) {
            return BoolBuiltin.kAppOf(value);
        } else if (sort.equals(Sort.BUILTIN_INT) || sort.equals(Sort.INT)) {
            return IntBuiltin.kAppOf(value);
        } else if (sort.equals(Sort.BUILTIN_FLOAT) || sort.equals(Sort.FLOAT)) {
            return FloatBuiltin.kAppOf(value);
        } else if (sort.equals(Sort.BUILTIN_STRING) || sort.equals(Sort.STRING)) {
            return StringBuiltin.kAppOf(StringUtil.unquoteKString(value));
        } else {
            return GenericToken.kAppOf(sort, value);
        }
    }

    /**
     * Returns a {@link KApp} representing a {@link Token} with the sort and value specified by the given {@link Element} applied to an empty {@link KList}.
     *
     * @param element
     * @return
     */
    public static KApp kAppOf(Element element) {
        Sort sort = Sort.of(element.getAttribute(Constants.SORT_sort_ATTR));
        if (sort.equals(Sort.BUILTIN_BOOL)) {
            return KApp.of(new BoolBuiltin(element));
        } else if (sort.equals(Sort.BUILTIN_INT)) {
            return KApp.of(new IntBuiltin(element));
        } else if (sort.equals(Sort.BUILTIN_STRING)) {
            return KApp.of(new StringBuiltin(element));
        } else if (sort.equals(Sort.BUILTIN_FLOAT)) {
            return KApp.of(new FloatBuiltin(element));
        } else {
            return KApp.of(new GenericToken(element));
        }
    }

    protected Token() {
    }

    protected Token(Element element) {
        super(element);
    }

    public abstract Sort tokenSort();

    /**
     * Returns a {@link String} representing the (uninterpreted) value of the token.
     *
     * @return
     */
    public abstract String value();

    @Override
    public Term shallowCopy() {
        /* this object is immutable */
        return this;
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Context.HASH_PRIME + tokenSort().hashCode();
        hash = hash * org.kframework.kil.loader.Context.HASH_PRIME + value().hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof Token)) {
            return false;
        }

        Token token = (Token) object;
        return tokenSort().equals(token.tokenSort()) && value().equals(token.value());
    }

    @Override
    public String toString() {
        // TODO (BUG): has extra quotations when #Sort string
        return "#token(\"" + tokenSort() + "\", " + StringUtil.enquoteKString(value()) + ")";
    }

}
