// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins.primitives;

/**
 * @author AndreiS
 */
public class OverflowArithmeticResult<T extends Number> {

    /**
     * Value of the arithmetic operation
     */
    public final T value;
    /**
     * True if the arithmetic operation overflows
     */
    public final boolean overflow;

    OverflowArithmeticResult(T value, boolean overflow) {
        this.value = value;
        this.overflow = overflow;
    }

}
