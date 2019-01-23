// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.attributes.Att;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.compile.FloatBuiltin;
import org.kframework.kil.Attribute;
import org.kframework.mpfr.BigFloat;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

public class FloatToken extends Token {

    public static final Sort SORT = Sort.FLOAT;

    /* Token cache */
    private static final Map<Integer, Map<BigFloat, FloatToken>> cache = new ConcurrentHashMap<>();

    private final BigFloat value;
    private final int exponent;

    private FloatToken(BigFloat value, int exponent) {
        this.value = value;
        this.exponent = exponent;
    }

    /**
     * Returns a {@code FloatToken} representation of the given {@link BigFloat} javaBackendValue in the
     * specified exponent range. The {@code FloatToken} instances are cached to ensure
     * uniqueness (subsequent invocations of this method with the same {@code FloatToken} javaBackendValue
     * and {@code int} exponent return the same {@code FloatToken} object).
     */
    public static FloatToken of(BigFloat value, int exponent) {
        Map<BigFloat, FloatToken> exponentCache = cache.computeIfAbsent(exponent, ConcurrentHashMap::new);
        return exponentCache.computeIfAbsent(value, v -> new FloatToken(v, exponent));
    }

    public static FloatToken of(String value) {
        Pair<BigFloat, Integer> pair = FloatBuiltin.parseKFloat(value);
        return of(pair.getLeft(), pair.getRight());
    }

    /**
     * Returns a {@link BigFloat} representation of the (interpreted) javaBackendValue of this FloatToken.
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
    public Sort sort() {
        return SORT;
    }

    /**
     * Returns a {@code String} representation of the (uninterpreted) javaBackendValue of this FloatToken.
     */
    @Override
    public String javaBackendValue() {
        return FloatBuiltin.printKFloat(value) + FloatBuiltin.printKFloatSuffix(value, exponent);
    }

    @Override
    protected int computeHash() {
        return value.hashCode() * 31 + exponent;
    }

    @Override
    public boolean equals(Object object) {
        /* IntToken instances are cached */
        return this == object;
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    /**
     * Get the exponent and significand of a term of sort Float assumed to have
     * a exponent and a significand attributes. Throws an error if the term does
     * not declare them.
     */
    public static Pair<Integer, Integer> getExponentAndSignificandOrDie(Att t) {
        Pair<Integer, Integer> pair = getExponentAndSignificand(t);
        if (pair == null) {
            throw KEMException.criticalError("Expected floating point number variable to declare an exponent and a significand." +
                    " For example, F:Float{exponent(11), significand(53)} for a double-precision floating point number.");
        }
        return pair;
    }

    public static Pair<Integer, Integer> getExponentAndSignificand(Att t) {
        String exponent = t.getOptional(Attribute.EXPONENT_KEY).orElse(null);
        String significand = t.getOptional(Attribute.SIGNIFICAND_KEY).orElse(null);
        if (exponent == null || significand == null) {
            return null;
        }
        try {
            return Pair.of(Integer.parseInt(exponent), Integer.parseInt(significand));
        } catch (NumberFormatException e) {
            throw KEMException.criticalError("Expected variable attributes 'exponent' and 'significand' to " +
                    "be integers, found: " + t.getOptional(Attribute.EXPONENT_KEY).orElse(null) + " " + t.getOptional(Attribute.SIGNIFICAND_KEY).orElse(null), e);
        }
    }

    /**
     * Returns the cached instance rather than the de-serialized instance if there is a cached
     * instance.
     */
    private Object readResolve() {
        Map<BigFloat, FloatToken> exponentCache = cache.computeIfAbsent(exponent, ConcurrentHashMap::new);
        return exponentCache.computeIfAbsent(value, v -> this);
    }

}
