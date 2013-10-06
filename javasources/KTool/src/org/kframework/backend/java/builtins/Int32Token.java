package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.HashMap;
import java.util.Map;


/**
 * An integer token. Integer tokens have arbitrary precision.
 *
 * @author Pat
 */
public class Int32Token extends Token {

    public static final String SORT_NAME = "Int32";

    /* Int32Token cache */
    private static final Map<Integer, Int32Token> cache = new HashMap<Integer, Int32Token>();

    /* counter for generating fresh Int32Token values */
    private static int freshValue = 0;

    /* Integer value wrapped by this Int32Token */
    private final int value;

    private Int32Token(int value) {
        this.value = value;
    }

    public static Int32Token fresh() {
        ++freshValue;
        return of(freshValue);
    }

    /**
     * Returns a {@code Int32Token} representation of the given {@link Integer} value. The
     * {@code Int32Token} instances are cached to ensure uniqueness (subsequent invocations of this
     * method with the same {@code Integer} value return the same {@code Int32Token} object).
     */
    public static Int32Token of(int value) {

        Int32Token intToken = cache.get(value);
        if (intToken == null) {
            intToken = new Int32Token(value);
            cache.put(value, intToken);
        }
        return intToken;
    }

    /**
     * Returns an {@code int} representation of the (interpreted) value of this
     * Int32Token.
     * @throws ArithmeticException Integer does not fit in an int.
     */
    public int intValue() {
      return value;
    }

    /**
     * Returns a {@code byte} representation of the (interpreted) value of this
     * Int32Token. Assumes an unsigned value in the range 0-255.
     * @throws ArithmeticException Integer is not in the range of an unsigned byte.
     */
    public byte unsignedByteValue() {
        if (value > 255) {
            throw new ArithmeticException();
        }
        if (value < 0) {
            throw new ArithmeticException();
        }
        return (byte)value;
    }

    /**
     * Returns a {@code String} representation of the sort of this Int32Token.
     */
    @Override
    public String sort() {
        return Int32Token.SORT_NAME;
    }

    /**
     * Returns a {@code String} representation of the (uninterpreted) value of this Int32Token.
     */
    @Override
    public String value() {
      return Integer.toString(value);
    }

    @Override
    public int hashCode() {
        return value;
    }

    @Override
    public boolean equals(Object object) {
        /* Int32Token instances are cached */
        return this == object;
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        unifier.unify(this, patten);
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
        Int32Token intToken = cache.get(value);
        if (intToken == null) {
            intToken = this;
            cache.put(value, intToken);
        }
        return intToken;
    }

}
