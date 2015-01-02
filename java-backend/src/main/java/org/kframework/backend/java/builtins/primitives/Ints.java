// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins.primitives;

import com.google.common.primitives.UnsignedInts;

/**
 * @author AndreiS
 */
public final class Ints {

    private Ints() { }

    public static OverflowArithmeticResult<Integer> checkedAdd(int a, int b) {
        long result = (long) a + (long) b;
        return new OverflowArithmeticResult<>((int) result, result != (int) result);
    }

    public static OverflowArithmeticResult<Integer> checkedUnsignedAdd(int a, int b) {
        long result = UnsignedInts.toLong(a) + UnsignedInts.toLong(b);
        return new OverflowArithmeticResult<>((int) result, result != (int) result);
    }

    public static OverflowArithmeticResult<Integer> checkedSub(int a, int b) {
        long result = (long) a - (long) b;
        return new OverflowArithmeticResult<>((int) result, result != (int) result);
    }

    public static OverflowArithmeticResult<Integer> checkedUnsignedSub(int a, int b) {
        long result = UnsignedInts.toLong(a) - UnsignedInts.toLong(b);
        return new OverflowArithmeticResult<>((int) result, result != (int) result);
    }

    public static OverflowArithmeticResult<Integer> checkedMul(int a, int b) {
        long result = (long) a * (long) b;
        return new OverflowArithmeticResult<>((int) result, result != (int) result);
    }

    public static OverflowArithmeticResult<Integer> checkedUnsignedMul(int a, int b) {
        long result = UnsignedInts.toLong(a) * UnsignedInts.toLong(b);
        return new OverflowArithmeticResult<>((int) result, result != (int) result);
    }

    public static OverflowArithmeticResult<Integer> checkedDiv(int a, int b) {
        long result = (long) a / (long) b;
        return new OverflowArithmeticResult<>((int) result, result != (int) result);
    }

    public static OverflowArithmeticResult<Integer> checkedRem(int a, int b) {
        /* the overflow flag for srem is set if the associated sdiv overflows */
        int result = a % b;
        long divisionResult = (long) a / (long) b;
        return new OverflowArithmeticResult<>(result, divisionResult != (int) divisionResult);
    }

}
