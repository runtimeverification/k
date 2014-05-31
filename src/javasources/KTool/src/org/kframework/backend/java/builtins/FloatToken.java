// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import java.util.HashMap;
import java.util.Map;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.FloatBuiltin;
import org.kframework.mpfr.BigFloat;

public class FloatToken extends Token {

    public static final String SORT_NAME = "Float";
    
    /* Token cache */
    private static final Map<Integer, Map<BigFloat, FloatToken>> cache = new HashMap<>();
    
    private final BigFloat value;
    private final int exponent;
    
    private FloatToken(BigFloat value, int exponent) {
        this.value = value;
        this.exponent = exponent;
    }
    
    /**
     * Returns a {@code FloatToken} representation of the given {@link BigFloat} value in the
     * specified exponent range. The {@code FloatToken} instances are cached to ensure
     * uniqueness (subsequent invocations of this method with the same {@code FloatToken} value
     * and {@code int} exponent return the same {@code FloatToken} object).
     */
    public static FloatToken of(BigFloat value, int exponent) {
        Map<BigFloat, FloatToken> exponentCache = cache.get(exponent);
        if (exponentCache == null) {
            exponentCache = new HashMap<>();
            cache.put(exponent, exponentCache);
        }

        FloatToken cachedFloatToken = exponentCache.get(value);
        if (cachedFloatToken == null) {
            cachedFloatToken = new FloatToken(value, exponent);
            exponentCache.put(value, cachedFloatToken);
        }

        return cachedFloatToken;
    }
    
    public static FloatToken of(String value) {
        Pair<BigFloat, Integer> pair = FloatBuiltin.parseKFloat(value);
        return of(pair.getLeft(), pair.getRight());
    }
    
    /**
     * Returns a {@link BigFloat} representation of the (interpreted) value of this FloatToken.
     */
    public BigFloat bigFloatValue() {
        return value;
    }
    
    /**
     * Returns an integer containing the number of bits in the exponent range of this FloatToken.
     */
    public int exponent() {
        return exponent;
    }

    
    /**
     * Returns a {@code String} representation of the sort of this FlaotToken.
     */
    @Override
    public String sort() {
        return FloatToken.SORT_NAME;
    }

    /**
     * Returns a {@code String} representation of the (uninterpreted) value of this FloatToken.
     */
    @Override
    public String value() {
        return FloatBuiltin.printKFloat(value) + FloatBuiltin.printKFloatSuffix(value, exponent);
    }
    
    @Override
    public int computeHash() {
        return value.hashCode() * 31 + exponent;
    }

    @Override
    public boolean equals(Object object) {
        /* IntToken instances are cached */
        return this == object;
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }
    
    @Override
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
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
        Map<BigFloat, FloatToken> exponentCache = cache.get(exponent);
        if (exponentCache == null) {
            exponentCache = new HashMap<>();
            cache.put(exponent, exponentCache);
        }

        FloatToken cachedFloatToken = exponentCache.get(value);
        if (cachedFloatToken == null) {
            cachedFloatToken = this;
            exponentCache.put(value, cachedFloatToken);
        }

        return cachedFloatToken;
    }

}
