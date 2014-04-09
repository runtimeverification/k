package org.kframework.backend.java.builtins;

import com.google.common.collect.Lists;
import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Term;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.ImmutableList;


/**
 * Implementation of a bit vector using {@link java.math.BigInteger}.
 *
 * @author AndreiS
 */
public final class BigIntegerBitVector extends BitVector<BigInteger> {

    private BigIntegerBitVector(BigInteger value, int bitwidth) {
        super(value, bitwidth);
    }

    public static BigIntegerBitVector of(BigInteger value, int bitwidth) {
        assert bitwidth > 0;

        return new BigIntegerBitVector(value, bitwidth);
    }

    @Override
    public boolean isZero() {
        return unsignedValue().equals(BigInteger.ZERO);
    }

    private boolean checkSignedOverflow(BigInteger bigInteger) {
        return bigInteger.compareTo(signedMin()) < 0 || bigInteger.compareTo(signedMax()) > 0;
    }

    private boolean checkUnsignedOverflow(BigInteger bigInteger) {
        return bigInteger.compareTo(unsignedMin()) < 0 || bigInteger.compareTo(unsignedMax()) > 0;
    }

    private BigInteger signedMin() {
        return BigInteger.ZERO.subtract(BigInteger.ONE.shiftLeft(bitwidth - 1));
    }

    private BigInteger signedMax() {
        return BigInteger.ONE.shiftLeft(bitwidth - 1).subtract(BigInteger.ONE);
    }

    private BigInteger unsignedMin() {
        return BigInteger.ZERO;
    }

    private BigInteger unsignedMax() {
        return BigInteger.ONE.shiftLeft(bitwidth).subtract(BigInteger.ONE);
    }

    @Override
    public BigInteger signedValue() {
        return value
                .add(BigInteger.ONE.shiftLeft(bitwidth - 1))
                .mod(BigInteger.ONE.shiftLeft(bitwidth))
                .subtract(BigInteger.ONE.shiftLeft(bitwidth - 1));
    }

    @Override
    public BigInteger unsignedValue() {
        return value.mod(BigInteger.ONE.shiftLeft(bitwidth));
    }

    @Override
    public BitVector<BigInteger> add(BitVector<BigInteger> bitVector) {
        return BigIntegerBitVector.of(value.add(bitVector.value), bitwidth);
    }

    @Override
    public BitVector<BigInteger> sub(BitVector<BigInteger> bitVector) {
        return BigIntegerBitVector.of(value.subtract(bitVector.value), bitwidth);
    }

    @Override
    public BitVector<BigInteger> mul(BitVector<BigInteger> bitVector) {
        return BigIntegerBitVector.of(value.multiply(bitVector.value), bitwidth);
    }

    @Override
    public BuiltinList sdiv(BitVector<BigInteger> bitVector) {
        if (!bitVector.signedValue().equals(BigInteger.ZERO)) {
            BigInteger result = signedValue().divide(bitVector.signedValue());
            return getBuiltinList(result, checkSignedOverflow(result));
        } else {
            return null;
        }
    }

    @Override
    public BuiltinList srem(BitVector<BigInteger> bitVector) {
        if (!bitVector.signedValue().equals(BigInteger.ZERO)) {
            /* the overflow flag for srem is set if the associated sdiv overflows */
            BigInteger result = signedValue().remainder(bitVector.signedValue());
            return getBuiltinList(
                    signedValue().remainder(bitVector.signedValue()),
                    checkSignedOverflow(signedValue().divide(bitVector.signedValue())));
        } else {
            return null;
        }
    }

    @Override
    public BitVector<BigInteger> udiv(BitVector<BigInteger> bitVector) {
        if (!bitVector.unsignedValue().equals(BigInteger.ZERO)) {
            return BigIntegerBitVector.of(
                    unsignedValue().divide(bitVector.unsignedValue()),
                    bitwidth);
        } else {
            return null;
        }
    }

    @Override
    public BitVector<BigInteger> urem(BitVector<BigInteger> bitVector) {
        if (!bitVector.unsignedValue().equals(BigInteger.ZERO)) {
            return BigIntegerBitVector.of(
                    unsignedValue().remainder(bitVector.unsignedValue()),
                    bitwidth);
        } else {
            return null;
        }
    }

    @Override
    public BuiltinList sadd(BitVector<BigInteger> bitVector) {
        BigInteger result = signedValue().add(bitVector.signedValue());
        return getBuiltinList(result, checkSignedOverflow(result));
    }

    @Override
    public BuiltinList uadd(BitVector<BigInteger> bitVector) {
        BigInteger result = unsignedValue().add(bitVector.unsignedValue());
        return getBuiltinList(result, checkUnsignedOverflow(result));
    }

    @Override
    public BuiltinList ssub(BitVector<BigInteger> bitVector) {
        BigInteger result = signedValue().subtract(bitVector.signedValue());
        return getBuiltinList(result, checkSignedOverflow(result));
    }

    @Override
    public BuiltinList usub(BitVector<BigInteger> bitVector) {
        BigInteger result = unsignedValue().subtract(bitVector.unsignedValue());
        return getBuiltinList(result, checkUnsignedOverflow(result));
    }

    @Override
    public BuiltinList smul(BitVector<BigInteger> bitVector) {
        BigInteger result = signedValue().multiply(bitVector.signedValue());
        return getBuiltinList(result, checkSignedOverflow(result));
    }

    @Override
    public BuiltinList umul(BitVector<BigInteger> bitVector) {
        BigInteger result = unsignedValue().multiply(bitVector.unsignedValue());
        return getBuiltinList(result, checkUnsignedOverflow(result));
    }

    @Override
    public BitVector<BigInteger> shl(IntToken intToken) {
        return BigIntegerBitVector.of(value.shiftLeft(intToken.intValue()), bitwidth);
    }

    @Override
    public BitVector<BigInteger> ashr(IntToken intToken) {
        return BigIntegerBitVector.of(value.shiftRight(intToken.intValue()), bitwidth);
    }

    @Override
    public BitVector<BigInteger> lshr(IntToken intToken) {
        BigInteger widthMask = BigInteger.ONE.shiftLeft(bitwidth).subtract(BigInteger.ONE);
        return BigIntegerBitVector.of(
                value.and(widthMask).shiftRight(intToken.intValue()),
                bitwidth);
    }

    @Override
    public BitVector<BigInteger> and(BitVector<BigInteger> bitVector) {
        return BigIntegerBitVector.of(value.and(bitVector.value), bitwidth);
    }

    @Override
    public BitVector<BigInteger> or(BitVector<BigInteger> bitVector) {
        return BigIntegerBitVector.of(value.or(bitVector.value), bitwidth);
    }

    @Override
    public BitVector<BigInteger> xor(BitVector<BigInteger> bitVector) {
        return BigIntegerBitVector.of(value.xor(bitVector.value), bitwidth);
    }

    @Override
    public BoolToken slt(BitVector<BigInteger> bitVector) {
        return BoolToken.of(signedValue().compareTo(bitVector.signedValue()) < 0);
    }

    @Override
    public BoolToken ult(BitVector<BigInteger> bitVector) {
        return BoolToken.of(unsignedValue().compareTo(bitVector.unsignedValue()) < 0);
    }

    @Override
    public BoolToken sle(BitVector<BigInteger> bitVector) {
        return BoolToken.of(signedValue().compareTo(bitVector.signedValue()) <= 0);
    }

    @Override
    public BoolToken ule(BitVector<BigInteger> bitVector) {
        return BoolToken.of(unsignedValue().compareTo(bitVector.unsignedValue()) <= 0);
    }

    @Override
    public BoolToken sgt(BitVector<BigInteger> bitVector) {
        return BoolToken.of(signedValue().compareTo(bitVector.signedValue()) > 0);
    }

    @Override
    public BoolToken ugt(BitVector<BigInteger> bitVector) {
        return BoolToken.of(unsignedValue().compareTo(bitVector.unsignedValue()) > 0);
    }

    @Override
    public BoolToken sge(BitVector<BigInteger> bitVector) {
        return BoolToken.of(signedValue().compareTo(bitVector.signedValue()) >= 0);
    }

    @Override
    public BoolToken uge(BitVector<BigInteger> bitVector) {
        return BoolToken.of(unsignedValue().compareTo(bitVector.unsignedValue()) >= 0);
    }

    @Override
    public BoolToken eq(BitVector<BigInteger> bitVector) {
        return BoolToken.of(unsignedValue().equals(bitVector.unsignedValue()));
    }

    @Override
    public BoolToken ne(BitVector<BigInteger> bitVector) {
        return BoolToken.of(!unsignedValue().equals(bitVector.unsignedValue()));
    }

    @Override
    public List<BitVector> toDigits(int digitBase) {
        assert digitBase > 0;

        List<BitVector> digits = new ArrayList<>();
        BigInteger unsignedValue = unsignedValue();
        for (int i = 0; i * digitBase < bitwidth; ++i) {
            digits.add(BitVector.of(
                    unsignedValue.remainder(BigInteger.ONE.shiftLeft(digitBase)),
                    digitBase));
            unsignedValue = unsignedValue.shiftRight(digitBase);
        }

        return Lists.reverse(digits);
    }

    private BuiltinList getBuiltinList(BigInteger result, boolean overflow) {
        return new BuiltinList(ImmutableList.<Term>of(
                BitVector.of(result, bitwidth),
                BoolToken.of(overflow)));
    }

}
