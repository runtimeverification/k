// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import java.math.RoundingMode;

import org.kframework.backend.java.kil.*;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

/**
 * Table of {@code public static} methods on builtin floats.
 *
 * @author: TraianSF
 */
public class BuiltinFloatOperations {

    private static BinaryMathContext getMathContext(FloatToken term1, FloatToken term2) {
        getExponent(term1, term2);
        if (term1.bigFloatValue().precision() != term2.bigFloatValue().precision()) {
            throw new IllegalArgumentException("mismatch precision: "
                    + "first argument precision is represented on " + term1.bigFloatValue().precision() + " bits "
                    + "while second argument precision is represented on " + term2.bigFloatValue().precision() + "bits");
        }
        return getMathContext(term1);
    }
    
    private static BinaryMathContext getMathContext(FloatToken term) {
        return new BinaryMathContext(term.bigFloatValue().precision(), term.exponent());
    }
    
    private static int getExponent(FloatToken term1, FloatToken term2) {
        if (term1.exponent() != term2.exponent()) {
            throw new IllegalArgumentException("mismatch exponent: "
                + "first argument exponent is represented on " + term1.exponent() + " bits "
                + "while second argument exponent is represented on " + term2.exponent() + "bits");
        }
        return term1.exponent();
    }
    
    public static IntToken precision(FloatToken term, TermContext context) {
        return IntToken.of(term.bigFloatValue().precision());
    }
    
    public static IntToken exponent(FloatToken term, TermContext context) {
        BinaryMathContext mc = getMathContext(term);
        return IntToken.of(term.bigFloatValue().exponent(mc.minExponent, mc.maxExponent));
    }
    
    public static IntToken exponentBits(FloatToken term, TermContext context) {
        return IntToken.of(term.exponent());
    }
    
    public static BoolToken sign(FloatToken term, TermContext context) {
        return BoolToken.of(term.bigFloatValue().sign());
    }
    
    public static BitVector<?> significand(FloatToken term, TermContext context) {
        BinaryMathContext mc = getMathContext(term);
        return BitVector.of(term.bigFloatValue().significand(mc.minExponent, mc.maxExponent), mc.precision);
    }
    
    public static FloatToken add(FloatToken term1, FloatToken term2, TermContext context) {
        return FloatToken.of(term1.bigFloatValue().add(term2.bigFloatValue(), 
                getMathContext(term1, term2)), getExponent(term1, term2));
    }

     public static FloatToken sub(FloatToken term1, FloatToken term2, TermContext context) {
         return FloatToken.of(term1.bigFloatValue().subtract(term2.bigFloatValue(), 
                 getMathContext(term1, term2)), getExponent(term1, term2));
    }

    public static FloatToken mul(FloatToken term1, FloatToken term2, TermContext context) {
         return FloatToken.of(term1.bigFloatValue().multiply(term2.bigFloatValue(), 
                 getMathContext(term1, term2)), getExponent(term1, term2));
    }
    
    public static FloatToken div(FloatToken term1, FloatToken term2, TermContext context) {
        return FloatToken.of(term1.bigFloatValue().divide(term2.bigFloatValue(), 
                getMathContext(term1, term2)), getExponent(term1, term2));
    }
    
    public static FloatToken rem(FloatToken term1, FloatToken term2, TermContext context) {
        return FloatToken.of(term1.bigFloatValue().remainder(term2.bigFloatValue(), 
                getMathContext(term1, term2)), getExponent(term1, term2));
    }
    
    public static FloatToken pow(FloatToken term1, FloatToken term2, TermContext context) {
        return FloatToken.of(term1.bigFloatValue().pow(term2.bigFloatValue(), 
                getMathContext(term1, term2)), getExponent(term1, term2));
    }
    
    public static FloatToken root(FloatToken term1, IntToken term2, TermContext context) {
        return FloatToken.of(term1.bigFloatValue().root(term2.intValue(), 
                getMathContext(term1)), term1.exponent());
    }

    public static FloatToken unaryMinus(FloatToken term, TermContext context) {
        return FloatToken.of(term.bigFloatValue().negate(
                getMathContext(term)), term.exponent());
    }
    
    public static FloatToken abs(FloatToken term, TermContext context) {
        return FloatToken.of(term.bigFloatValue().abs(
                getMathContext(term)), term.exponent());
    }
    
    public static FloatToken round(FloatToken term, IntToken precision, IntToken exponent, TermContext context) {
        if (exponent.intValue() < 2) {
            return null;
        }
        return FloatToken.of(term.bigFloatValue().round(
                new BinaryMathContext(precision.intValue(), exponent.intValue())),
                exponent.intValue());
    }
    
    public static FloatToken exp(FloatToken term, TermContext context) {
        return FloatToken.of(term.bigFloatValue().exp(
                getMathContext(term)), term.exponent());
    }
    
    public static FloatToken log(FloatToken term, TermContext context) {
        return FloatToken.of(term.bigFloatValue().log(
                getMathContext(term)), term.exponent());
    }
    
    public static FloatToken sin(FloatToken term, TermContext context) {
        return FloatToken.of(term.bigFloatValue().sin(
                getMathContext(term)), term.exponent());
    }
    
    public static FloatToken cos(FloatToken term, TermContext context) {
        return FloatToken.of(term.bigFloatValue().cos(
                getMathContext(term)), term.exponent());
    }
    
    public static FloatToken tan(FloatToken term, TermContext context) {
        return FloatToken.of(term.bigFloatValue().tan(
                getMathContext(term)), term.exponent());
    }
    
    public static FloatToken asin(FloatToken term, TermContext context) {
        return FloatToken.of(term.bigFloatValue().asin(
                getMathContext(term)), term.exponent());
    }
    
    public static FloatToken acos(FloatToken term, TermContext context) {
        return FloatToken.of(term.bigFloatValue().acos(
                getMathContext(term)), term.exponent());
    }
    
    public static FloatToken atan(FloatToken term, TermContext context) {
        return FloatToken.of(term.bigFloatValue().atan(
                getMathContext(term)), term.exponent());
    }
    
    public static FloatToken atan2(FloatToken term1, FloatToken term2, TermContext context) {
        return FloatToken.of(BigFloat.atan2(term1.bigFloatValue(), term2.bigFloatValue(),
                getMathContext(term1, term2)), getExponent(term1, term2));
    }

    public static FloatToken max(FloatToken term1, FloatToken term2, TermContext context) {
        return FloatToken.of(BigFloat.max(term1.bigFloatValue(), term2.bigFloatValue(),
                getMathContext(term1, term2)), getExponent(term1, term2));
    }
    
    public static FloatToken min(FloatToken term1, FloatToken term2, TermContext context) {
        return FloatToken.of(BigFloat.min(term1.bigFloatValue(), term2.bigFloatValue(),
                getMathContext(term1, term2)), getExponent(term1, term2));
    }

    public static BoolToken eq(FloatToken term1, FloatToken term2, TermContext context) {
        return BoolToken.of(term1.bigFloatValue().equalTo(term2.bigFloatValue()));
    }

    public static BoolToken gt(FloatToken term1, FloatToken term2, TermContext context) {
        return BoolToken.of(term1.bigFloatValue().greaterThan(term2.bigFloatValue()));
    }

    public static BoolToken ge(FloatToken term1, FloatToken term2, TermContext context) {
        return BoolToken.of(term1.bigFloatValue().greaterThanOrEqualTo(term2.bigFloatValue()));
    }

    public static BoolToken lt(FloatToken term1, FloatToken term2, TermContext context) {
        return BoolToken.of(term1.bigFloatValue().lessThan(term2.bigFloatValue()));
    }

    public static BoolToken le(FloatToken term1, FloatToken term2, TermContext context) {
        return BoolToken.of(term1.bigFloatValue().lessThanOrEqualTo(term2.bigFloatValue()));
    }
    
    public static FloatToken int2float(IntToken term, IntToken precision, IntToken exponent, TermContext context) {
        return FloatToken.of(new BigFloat(term.bigIntegerValue(), 
                new BinaryMathContext(precision.intValue(), exponent.intValue())), exponent.intValue());
    }
    
    public static IntToken float2int(FloatToken term, TermContext context) {
        return IntToken.of(term.bigFloatValue().rint(getMathContext(term)).toBigIntegerExact());
    }
    
    public static FloatToken ceil(FloatToken term, TermContext context) {
        return FloatToken.of(term.bigFloatValue().rint(getMathContext(term)
                .withRoundingMode(RoundingMode.CEILING)), term.exponent());
    }
    
    public static FloatToken floor(FloatToken term, TermContext context) {
        return FloatToken.of(term.bigFloatValue().rint(getMathContext(term)
                .withRoundingMode(RoundingMode.FLOOR)), term.exponent());
    }
}
