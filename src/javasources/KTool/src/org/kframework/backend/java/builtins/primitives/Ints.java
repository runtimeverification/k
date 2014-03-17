package org.kframework.backend.java.builtins.primitives;

import com.google.common.primitives.UnsignedInts;

/**
 * @author AndreiS
 */
public class Ints {

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

}
