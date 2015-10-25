// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.MaximalSharing;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.math.BigInteger;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;


/**
 * An integer token. Integer tokens have arbitrary precision.
 *
 * @author AndreiS
 */
public final class IntToken extends Token {

    public static final Sort SORT = Sort.INT;

    /* BigInteger value wrapped by this IntToken */
    private final BigInteger value;

    private IntToken(BigInteger value) {
        this.value = value;
    }

    /**
     * Returns a {@code IntToken} representation of the given {@link BigInteger} value. The
     * {@code IntToken} instances are cached to ensure uniqueness (subsequent invocations of this
     * method with the same {@code BigInteger} value return the same {@code IntToken} object).
     */
    public static IntToken of(BigInteger value) {
        assert value != null;
        return new IntToken(value);
    }

    public static IntToken of(long value) {
        return of(BigInteger.valueOf(value));
    }

    public static IntToken of(String value) {
        try {
            return IntToken.of(new BigInteger(value));
        } catch (NumberFormatException e) {
            if (value.codePointCount(0, value.length()) == 1) {
                int numericValue = Character.getNumericValue(value.codePointAt(0));
                if (numericValue >= 0) {
                    return IntToken.of(numericValue);
                }
            }
            throw e;
        }
    }

    /**
     * Returns a {@link BigInteger} representation of the (interpreted) value of this IntToken.
     */
    public BigInteger bigIntegerValue() {
        return value;
    }

    /**
     * Returns an {@code int} representation of the (interpreted) value of this
     * IntToken.
     * @throws ArithmeticException Integer does not fit in an int.
     */
    public int intValue() {
        if (value.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) > 0) {
            throw new ArithmeticException();
        }
        if (value.compareTo(BigInteger.valueOf(Integer.MIN_VALUE)) < 0) {
            throw new ArithmeticException();
        }
        return (int)value.longValue();
    }

    /**
     * Returns a {@code long} representation of the (interpreted) value of this
     * IntToken.
     * @throws ArithmeticException Integer does not fit in a long.
     */
    public long longValue() {
        if (value.compareTo(BigInteger.valueOf(Long.MAX_VALUE)) > 0) {
            throw new ArithmeticException();
        }
        if (value.compareTo(BigInteger.valueOf(Long.MIN_VALUE)) < 0) {
            throw new ArithmeticException();
        }
        return value.longValue();
    }

    /**
     * Returns a {@code byte} representation of the (interpreted) value of this
     * IntToken. Assumes an unsigned value in the range 0-255.
     * @throws ArithmeticException Integer is not in the range of an unsigned byte.
     */
    public byte unsignedByteValue() {
        if (value.compareTo(BigInteger.valueOf(255)) > 0) {
            throw new ArithmeticException();
        }
        if (value.compareTo(BigInteger.valueOf(0)) < 0) {
            throw new ArithmeticException();
        }
        return (byte)value.longValue();
    }

    @Override
    public Sort sort() {
        return SORT;
    }

    /**
     * Returns a {@code String} representation of the (uninterpreted) value of this IntToken.
     */
    @Override
    public String value() {
        return value.toString();
    }

    @Override
    protected int computeHash() {
        return value.hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        IntToken intToken = (IntToken) o;

        return value.equals(intToken.value);

    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}
