package org.kframework.backend.java.builtins;

import org.kframework.backend.java.builtins.primitives.Ints;
import org.kframework.backend.java.builtins.primitives.OverflowArithmeticResult;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.Term;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.Lists;
import com.google.common.collect.ImmutableList;
import com.google.common.primitives.UnsignedInts;


/**
 * Wrapper around java primitive int.
 *
 * @author AndreiS
 */
public class Int32Token extends BitVector<Integer> {

    private Int32Token(int value) {
        super(value, Integer.SIZE);
    }

    public static Int32Token of(int value) {
        return new Int32Token(value);
    }

    @Override
    public boolean isZero() {
        return value == 0;
    }

    @Override
    public BigInteger signedValue() {
        return BigInteger.valueOf(value);
    }

    @Override
    public BigInteger unsignedValue() {
        return BigInteger.valueOf(UnsignedInts.toLong(value));
    }

    @Override
    public Int32Token add(BitVector<Integer> bitVector) {
        return Int32Token.of(value + bitVector.value);
    }

    @Override
    public Int32Token sub(BitVector<Integer> bitVector) {
        return Int32Token.of(value - bitVector.value);
    }

    @Override
    public Int32Token mul(BitVector<Integer> bitVector) {
        return Int32Token.of(value * bitVector.value);
    }

    @Override
    public BuiltinList sdiv(BitVector<Integer> bitVector) {
        if (bitVector.value != 0) {
            return makeBuiltinListOfOverflowArithmeticResult(Ints.checkedDiv(value, bitVector.value));
        } else {
            return null;
        }
    }

    @Override
    public BuiltinList srem(BitVector<Integer> bitVector) {
        if (bitVector.value != 0) {
            return makeBuiltinListOfOverflowArithmeticResult(Ints.checkedRem(value, bitVector.value));
        } else {
            return null;
        }
    }

    @Override
    public Int32Token udiv(BitVector<Integer> bitVector) {
        if (bitVector.value != 0) {
            return Int32Token.of(UnsignedInts.divide(value, bitVector.value));
        } else {
            return null;
        }
    }

    @Override
    public Int32Token urem(BitVector<Integer> bitVector) {
        if (bitVector.value != 0) {
            return Int32Token.of(UnsignedInts.remainder(value, bitVector.value));
        } else {
            return null;
        }
    }

    @Override
    public BuiltinList sadd(BitVector<Integer> bitVector) {
        return makeBuiltinListOfOverflowArithmeticResult(Ints.checkedAdd(value, bitVector.value));
    }

    @Override
    public BuiltinList uadd(BitVector<Integer> bitVector) {
        return makeBuiltinListOfOverflowArithmeticResult(
                Ints.checkedUnsignedAdd(value, bitVector.value));
    }

    @Override
    public BuiltinList ssub(BitVector<Integer> bitVector) {
        return makeBuiltinListOfOverflowArithmeticResult(Ints.checkedSub(value, bitVector.value));
    }

    @Override
    public BuiltinList usub(BitVector<Integer> bitVector) {
        return makeBuiltinListOfOverflowArithmeticResult(
                Ints.checkedUnsignedSub(value, bitVector.value));
    }

    @Override
    public BuiltinList smul(BitVector<Integer> bitVector) {
        return makeBuiltinListOfOverflowArithmeticResult(Ints.checkedMul(value, bitVector.value));
    }

    @Override
    public BuiltinList umul(BitVector<Integer> bitVector) {
        return makeBuiltinListOfOverflowArithmeticResult(
                Ints.checkedUnsignedMul(value, bitVector.value));
    }

    @Override
    public Int32Token shl(IntToken intToken) {
        return Int32Token.of(value << intToken.intValue());
    }

    @Override
    public Int32Token ashr(IntToken intToken) {
        return Int32Token.of(value >> intToken.intValue());
    }

    @Override
    public Int32Token lshr(IntToken intToken) {
        /* cast to long to avoid sign extension */
        return Int32Token.of((int) (UnsignedInts.toLong(value) >> intToken.intValue()));
    }

    @Override
    public Int32Token and(BitVector<Integer> bitVector) {
        return Int32Token.of(value & bitVector.value);
    }

    @Override
    public Int32Token or(BitVector<Integer> bitVector) {
        return Int32Token.of(value | bitVector.value);
    }

    @Override
    public Int32Token xor(BitVector<Integer> bitVector) {
        return Int32Token.of(value ^ bitVector.value);
    }

    @Override
    public BoolToken slt(BitVector<Integer> bitVector) {
        return BoolToken.of(value < bitVector.value);
    }

    @Override
    public BoolToken ult(BitVector<Integer> bitVector) {
        return BoolToken.of(UnsignedInts.compare(value, bitVector.value) < 0);
    }

    @Override
    public BoolToken sle(BitVector<Integer> bitVector) {
        return BoolToken.of(value <= bitVector.value);
    }

    @Override
    public BoolToken ule(BitVector<Integer> bitVector) {
        return BoolToken.of(UnsignedInts.compare(value, bitVector.value) <= 0);
    }

    @Override
    public BoolToken sgt(BitVector<Integer> bitVector) {
        return BoolToken.of(value > bitVector.value);
    }

    @Override
    public BoolToken ugt(BitVector<Integer> bitVector) {
        return BoolToken.of(UnsignedInts.compare(value, bitVector.value) > 0);
    }

    @Override
    public BoolToken sge(BitVector<Integer> bitVector) {
        return BoolToken.of(value >= bitVector.value);
    }

    @Override
    public BoolToken uge(BitVector<Integer> bitVector) {
        return BoolToken.of(UnsignedInts.compare(value, bitVector.value) >= 0);
    }

    @Override
    public BoolToken eq(BitVector<Integer> bitVector) {
        return BoolToken.of(value.equals(bitVector.value));
    }

    @Override
    public BoolToken ne(BitVector<Integer> bitVector) {
        return BoolToken.of(!value.equals(bitVector.value));
    }

    @Override
    public List<BitVector> toDigits(int digitBase) {
        assert digitBase > 0;

        List<BitVector> digits = new ArrayList<>();
        long longValue = UnsignedInts.toLong(this.value);
        for (int i = 0; i * digitBase < Integer.SIZE;  ++i, longValue >>= digitBase) {
            digits.add(BitVector.of(longValue % (1 << digitBase), digitBase));
        }

        return Lists.reverse(digits);
    }

    @Override
    public boolean equals(Object object) {
        return object instanceof Int32Token && value.equals(((Int32Token) object).value);
    }

    @Override
    public int hashCode() {
        return value;
    }

    private static BuiltinList makeBuiltinListOfOverflowArithmeticResult(
            OverflowArithmeticResult<Integer> result) {
        return new BuiltinList(ImmutableList.<Term>of(
                Int32Token.of(result.value),
                BoolToken.of(result.overflow)));
    }

}
