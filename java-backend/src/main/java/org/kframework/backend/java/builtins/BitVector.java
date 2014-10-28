// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.math.BigInteger;
import java.util.List;


/**
 * Abstract class representing a bit vector (and integer on an arbitrary but fixed number of bits).
 * @author AndreiS
 *
 * @see include/builtins/mint.k
 */
public abstract class BitVector<T extends Number> extends Token {

    public static final Sort SORT = Sort.BIT_VECTOR;

    /**
     * Integer value wrapped by this BitVector. The signed value and the unsigned value of this
     * BitVector are guaranteed to be equal with {@code value} only on the last {@code bitwidth}
     * bits.
     *
     * @see #signedValue()
     * @see #unsignedValue()
     */
    protected final T value;
    /**
     * The bit width on which this integer is represented.
     */
    protected final int bitwidth;

    protected BitVector(T value, int bitwidth) {
        this.value = value;
        this.bitwidth = bitwidth;
    }

    /**
     * Returns a {@code BitVector} representation of the given big integer value on the given
     * bit width.
     */
    public static BitVector of(BigInteger value, int bitwidth) {
        assert bitwidth > 0;

        switch (bitwidth) {
            case Integer.SIZE:
                return Int32Token.of(value.intValue());
            default:
                return BigIntegerBitVector.of(value, bitwidth);
        }
    }

    /**
     * Returns a {@code BitVector} representation of the given long value on the given bit width.
     */
    public static BitVector of(long value, int bitwidth) {
        assert bitwidth > 0;

        switch (bitwidth) {
            case Integer.SIZE:
                return Int32Token.of(Long.valueOf(value).intValue());
            default:
                return BigIntegerBitVector.of(BigInteger.valueOf(value), bitwidth);
        }
    }

    /**
     * Returns the bit width of this BitVector.
     */
    public int bitwidth() {
        return bitwidth;
    }

    /**
     * Returns true if this BitVector is zero.
     */
    public abstract boolean isZero();

    /**
     * Returns an {@code BigInteger} representation of the signed value of this BitVector.
     */
    public abstract BigInteger signedValue();

    /**
     * Returns an {@code BigInteger} representation of the unsigned value of this BitVector.
     */
    public abstract BigInteger unsignedValue();

    @Override
    public Sort sort() {
        return SORT;
    }

    /**
     * Returns a {@code String} representation of the (uninterpreted) value of this BitVector.
     */
    @Override
    public String value() {
        return bitwidth + "'" + value.toString();
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
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + value.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + bitwidth;
        return hashCode;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    public abstract BitVector<T> add(BitVector<T> bitVector);
    public abstract BitVector<T> sub(BitVector<T> bitVector);
    public abstract BitVector<T> mul(BitVector<T> bitVector);

    public abstract BuiltinList sdiv(BitVector<T> bitVector);
    public abstract BuiltinList srem(BitVector<T> bitVector);

    public abstract BitVector<T> udiv(BitVector<T> bitVector);
    public abstract BitVector<T> urem(BitVector<T> bitVector);

    public abstract BuiltinList sadd(BitVector<T> bitVector);
    public abstract BuiltinList uadd(BitVector<T> bitVector);
    public abstract BuiltinList ssub(BitVector<T> bitVector);
    public abstract BuiltinList usub(BitVector<T> bitVector);
    public abstract BuiltinList smul(BitVector<T> bitVector);
    public abstract BuiltinList umul(BitVector<T> bitVector);

    public abstract BitVector<T> shl(IntToken intToken);
    public abstract BitVector<T> ashr(IntToken intToken);
    public abstract BitVector<T> lshr(IntToken intToken);

    public abstract BitVector<T> and(BitVector<T> bitVector);
    public abstract BitVector<T> or(BitVector<T> bitVector);
    public abstract BitVector<T> xor(BitVector<T> bitVector);

    public abstract BoolToken slt(BitVector<T> bitVector);
    public abstract BoolToken ult(BitVector<T> bitVector);
    public abstract BoolToken sle(BitVector<T> bitVector);
    public abstract BoolToken ule(BitVector<T> bitVector);
    public abstract BoolToken sgt(BitVector<T> bitVector);
    public abstract BoolToken ugt(BitVector<T> bitVector);
    public abstract BoolToken sge(BitVector<T> bitVector);
    public abstract BoolToken uge(BitVector<T> bitVector);
    public abstract BoolToken eq(BitVector<T> bitVector);
    public abstract BoolToken ne(BitVector<T> bitVector);

    public BitVector concatenate(BitVector bitVector) {
        return BitVector.of(
                unsignedValue().shiftLeft(bitVector.bitwidth).add(bitVector.unsignedValue()),
                bitwidth + bitVector.bitwidth);
    }
    public abstract BitVector extract(int beginIndex, int endIndex);

    public abstract List<BitVector> toDigits(int digitBitWidth, int count);

    public static BitVector fromDigits(List<BitVector> digits) {
        assert !digits.isEmpty();

        BigInteger value = BigInteger.ZERO;
        int bitwidth = 0;
        for (BitVector digit : digits) {
            /* value = value * 2^digit_bitwidth + digit */
            value = value.shiftLeft(digit.bitwidth).add(digit.unsignedValue());
            bitwidth += digit.bitwidth;
        }

        return BitVector.of(value, bitwidth);
    }

    /**
     * Get the bitwidth of a term of sort MInt assumed to have a bitwidth attribute.
     * Throws an error if the term does not declare one.
     */
    public static int getBitwidthOrDie(ASTNode t) {
        Integer bitwidth = getBitwidth(t);
        if (bitwidth == null) {
            throw KExceptionManager.criticalError("Expected machine integer variable to declare a bitwidth." +
                    " For example, M:MInt{bitwidth(32)} for a 32-bit integer.");
        }
        return bitwidth;
    }

    public static Integer getBitwidth(ASTNode t) {
        String bitwidth = t.getAttribute(Attribute.BITWIDTH_KEY);
        if (bitwidth == null) {
            return null;
        }
        try {
            return Integer.parseInt(bitwidth);
        } catch (NumberFormatException e) {
            throw KExceptionManager.criticalError("Expected variable attribute 'bitwidth' to " +
                    "be an integer, found: " + t.getAttribute("bitwidth"), e);
        }
    }

}
