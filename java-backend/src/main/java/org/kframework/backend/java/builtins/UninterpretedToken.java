// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.MaximalSharing;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import java.util.HashMap;
import java.util.Map;


/**
 * Represents an uninterpreted token which consists of the {@code String}
 * representation of a sort and a value.
 *
 * @author AndreiS
 */
public final class UninterpretedToken extends Token implements MaximalSharing {

    /* Token cache */
    private static final Map<Sort, Map<String, UninterpretedToken>> cache = new HashMap<>();

    private final Sort sort;
    private final String value;

    private UninterpretedToken(Sort sort, String value) {
        this.sort = sort;
        this.value = value;
    }

    /**
     * Returns a {@code UninterpretedToken} representation of a token of given sort and value. The
     * UninterpretedToken instances are cached to ensure uniqueness (subsequent invocations of
     * this method with the same sort and value return the same {@code UninterpretedToken} object).
     */
    public static UninterpretedToken of(Sort sort, String value) {
        Map<String, UninterpretedToken> sortCache = cache.get(sort);
        if (sortCache == null) {
            sortCache = new HashMap<String, UninterpretedToken>();
            cache.put(sort, sortCache);
        }

        UninterpretedToken cachedGenericToken = sortCache.get(value);
        if (cachedGenericToken == null) {
            cachedGenericToken = new UninterpretedToken(sort, value);
            sortCache.put(value, cachedGenericToken);
        }

        return cachedGenericToken;
    }

    @Override
    public Sort sort() {
        return sort;
    }

    /**
     * Returns a {@code String} representation of the value of this UninterpretedToken.
     */
    @Override
    public String value() {
        return value;
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + value.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + sort.hashCode();
        return hashCode;
    }

    @Override
    public boolean equals(Object object) {
        /* UninterpretedToken instances are cached */
        return this == object;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    /**
     * Returns the cached instance rather than the de-serialized instance if there is a cached
     * instance.
     */
    private Object readResolve() {
        Map<String, UninterpretedToken> sortCache = cache.get(sort);
        if (sortCache == null) {
            sortCache = new HashMap<String, UninterpretedToken>();
            cache.put(sort, sortCache);
        }

        UninterpretedToken cachedGenericToken = sortCache.get(value);
        if (cachedGenericToken == null) {
            cachedGenericToken = this;
            sortCache.put(value, cachedGenericToken);
        }

        return cachedGenericToken;
    }

}
