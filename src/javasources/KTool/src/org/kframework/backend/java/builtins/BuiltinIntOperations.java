// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;


import org.kframework.backend.java.kil.TermContext;

/**
 * Table of {@code public static} methods on builtin integers.
 *
 * @author: AndreiS
 */
public class BuiltinIntOperations {

    public static IntToken add(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().add(term2.bigIntegerValue()));
    }

    public static IntToken sub(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().subtract(term2.bigIntegerValue()));
    }

    public static IntToken mul(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().multiply(term2.bigIntegerValue()));
    }

    public static IntToken div(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().divide(term2.bigIntegerValue()));
    }

    public static IntToken rem(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().remainder(term2.bigIntegerValue()));
    }

    public static IntToken mod(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().mod(term2.bigIntegerValue()));
    }

    public static IntToken pow(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().pow(term2.bigIntegerValue().intValue()));
    }

    public static IntToken shl(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().shiftLeft(term2.bigIntegerValue().intValue()));
    }

    public static IntToken shr(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().shiftRight(term2.bigIntegerValue().intValue()));
    }

    public static IntToken not(IntToken term, TermContext context) {
        return IntToken.of(term.bigIntegerValue().not());
    }

    public static IntToken and(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().and(term2.bigIntegerValue()));
    }

    public static IntToken or(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().or(term2.bigIntegerValue()));
    }

    public static IntToken xor(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().xor(term2.bigIntegerValue()));
    }

    public static IntToken min(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().min(term2.bigIntegerValue()));
    }

    public static IntToken max(IntToken term1, IntToken term2, TermContext context) {
        return IntToken.of(term1.bigIntegerValue().max(term2.bigIntegerValue()));
    }

    public static IntToken abs(IntToken term, TermContext context) {
        return IntToken.of(term.bigIntegerValue().abs());
    }

    public static BoolToken eq(IntToken term1, IntToken term2, TermContext context) {
        return BoolToken.of(term1.bigIntegerValue().compareTo(term2.bigIntegerValue()) == 0);
    }

    public static BoolToken ne(IntToken term1, IntToken term2, TermContext context) {
        return BoolToken.of(term1.bigIntegerValue().compareTo(term2.bigIntegerValue()) != 0);
    }

    public static BoolToken gt(IntToken term1, IntToken term2, TermContext context) {
        return BoolToken.of(term1.bigIntegerValue().compareTo(term2.bigIntegerValue()) > 0);
    }

    public static BoolToken ge(IntToken term1, IntToken term2, TermContext context) {
        return BoolToken.of(term1.bigIntegerValue().compareTo(term2.bigIntegerValue()) >= 0);
    }

    public static BoolToken lt(IntToken term1, IntToken term2, TermContext context) {
        return BoolToken.of(term1.bigIntegerValue().compareTo(term2.bigIntegerValue()) < 0);
    }

    public static BoolToken le(IntToken term1, IntToken term2, TermContext context) {
        return BoolToken.of(term1.bigIntegerValue().compareTo(term2.bigIntegerValue()) <= 0);
    }

}
