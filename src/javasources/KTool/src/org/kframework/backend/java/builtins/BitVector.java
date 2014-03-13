package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import java.math.BigInteger;


/**
 * @author AndreiS
 */
public class BitVector<T extends Number> extends Token {

    public static final String SORT_NAME = "MInt";

    /**
     * Integer value wrapped by this BitVector.
     */
    protected final T value;
    /**
     * The bit width on which this integer is represented.
     */
    protected final int bitwidth;

    public BitVector(T value, int bitwidth) {
        this.value = value;
        this.bitwidth = bitwidth;
    }

    /**
     * Returns a {@code BitVector} representation of the given integer value on the given
     * bit width.
     */
    public static BitVector of(BigInteger value, int bitwidth) {
        switch (bitwidth) {
            case Byte.SIZE:
                return PrimitiveIntToken.of(value.byteValue());
            case Short.SIZE:
                return PrimitiveIntToken.of(value.shortValue());
            case Integer.SIZE:
                return PrimitiveIntToken.of(value.intValue());
            case Long.SIZE:
                return PrimitiveIntToken.of(value.longValue());
            default:
                return new BitVector<>(value, bitwidth);
        }

    }

    /**
     * Returns an {@code BigInteger} representation of the (interpreted) value of this BitVector.
     */
    public BigInteger bigIntegerValue() {
        if (this instanceof PrimitiveIntToken) {
            return BigInteger.valueOf(((PrimitiveIntToken) this).longValue());
        } else {
            return (BigInteger) value;
        }
    }

    /**
     * Returns the bit width of this BitVector.
     */
    public int bitwidth() {
        return bitwidth;
    }

    /**
     * Returns a {@code String} representation of the sort of this BitVector.
     */
    @Override
    public String sort() {
        return BitVector.SORT_NAME;
    }

    /**
     * Returns a {@code String} representation of the (uninterpreted) value of this BitVector.
     */
    @Override
    public String value() {
      return value.toString();
    }

    @Override
    public int hashCode() {
        if (hashCode == 0) {
            hashCode = 1;
            hashCode = hashCode * Utils.HASH_PRIME + value.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + bitwidth;
        }
        return hashCode;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof BitVector)) {
            return false;
        }

        BitVector bitVector = (BitVector) object;
        return value.equals(bitVector.value) && bitwidth == bitVector.bitwidth;
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

}
