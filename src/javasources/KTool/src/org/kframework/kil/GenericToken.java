// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

import java.util.Map;
import java.util.HashMap;

/**
 * Generic class representing an (uninterpreted) token.
 */
public class GenericToken extends Token {
    /* Token cache */
    private static Map<GenericToken, GenericToken> tokenCache = new HashMap<GenericToken, GenericToken>();
    /* KApp cache */
    private static Map<GenericToken, KApp> kAppCache = new HashMap<GenericToken, KApp>();

    /**
     * Returns a {@link GenericToken} of the given sort with the given value.
     *
     * @param sort
     *            different than #Bool, #Int, or #String
     * @param value
     * @return
     */
    public static GenericToken of(Sort sort, String value) {
        GenericToken genericToken = new GenericToken(sort, value);
        GenericToken cachedGenericToken = tokenCache.get(genericToken);
        if (cachedGenericToken == null) {
            cachedGenericToken = genericToken;
            tokenCache.put(genericToken, cachedGenericToken);
        }
        return cachedGenericToken;
    }

    /**
     * Returns a {@link KApp} representing a {@link GenericToken} of the given sort with the given value applied to an empty {@link KList}.
     *
     * @param sort
     *            different than #Bool, #Int, or #String
     * @param value
     * @return
     */
    public static KApp kAppOf(Sort sort, String value) {
        GenericToken genericToken = new GenericToken(sort, value);
        KApp kApp = kAppCache.get(genericToken);
        if (kApp == null) {
            kApp = KApp.of(genericToken);
            kAppCache.put(genericToken, kApp);
        }
        return kApp;
    }

    private final Sort tokenSort;
    private final String value;

    private GenericToken(Sort sort, String value) {
        this.tokenSort = sort;
        this.value = value;
    }

    protected GenericToken(Element element) {
        super(element);
        this.tokenSort = Sort.of(element.getAttribute(Constants.SORT_sort_ATTR));
        this.value = element.getAttribute(Constants.VALUE_value_ATTR);
    }

    @Override
    public Sort tokenSort() {
        return tokenSort;
    }

    /**
     * Returns a {@link String} representing the (uninterpreted) value of the token.
     *
     * @return
     */
    @Override
    public String value() {
        return value;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
}
