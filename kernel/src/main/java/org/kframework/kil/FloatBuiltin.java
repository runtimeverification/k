// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Visitor;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.w3c.dom.Element;

public class FloatBuiltin extends Token {

    /* Token cache */
    private static Map<Pair<BigFloat, Integer>, FloatBuiltin> tokenCache = new HashMap<>();

    /**
     * Returns a {@link FloatBuiltin} representing the given {@link BigFloat} value
     * and the given exponent range, in bits.
     *
     * @param value
     * @return
     */
    public static FloatBuiltin of(BigFloat value, Integer exponent) {
        assert value != null;
        Pair<BigFloat, Integer> key = Pair.of(value, exponent);
        FloatBuiltin floatBuiltin = tokenCache.get(key);
        if (floatBuiltin == null) {
            floatBuiltin = new FloatBuiltin(value, exponent);
            tokenCache.put(key, floatBuiltin);
        }
        return floatBuiltin;
    }

    /**
     * Returns a {@link FloatBuiltin} representing the given {@link double} value.
     *
     * @param value
     * @return
     */
    public static FloatBuiltin of(double value) {
        return of(new BigFloat(value, BinaryMathContext.BINARY64), BinaryMathContext.BINARY64_EXPONENT_BITS);
    }

    /**
     * Returns a {@link FloatBuiltin} representing the given {@link float} value.
     *
     * @param value
     * @return
     */
    public static FloatBuiltin of(float value) {
        return of(new BigFloat(value, BinaryMathContext.BINARY32), BinaryMathContext.BINARY32_EXPONENT_BITS);
    }

    /**
     * Returns a {@link FloatBuiltin} representing the given {@link String} value.
     *
     * @param value
     * @return
     */
    public static FloatBuiltin of(String value) {
        Pair<BigFloat, Integer> pair = FloatBuiltin.parseKFloat(value);
        return of(pair.getLeft(), pair.getRight());
    }

    /**
     * Returns a {@link KApp} representing a {@link FloatBuiltin} with the given {@link String} representation applied to an empty {@link KList}.
     *
     * @param value
     * @return
     */
    public static KApp kAppOf(String value) {
        assert value != null;

        return KApp.of(FloatBuiltin.of(value));
    }

    private final BigFloat value;
    private final int exponent;

    private FloatBuiltin(BigFloat value, int exponent) {
        this.value = value;
        this.exponent = exponent;
    }

    private static Pattern precisionAndExponent = Pattern.compile("(.*)[pP](\\d+)[xX](\\d+)");
    public static Pair<BigFloat, Integer> parseKFloat(String s) {
        try {
            Matcher m = precisionAndExponent.matcher(s);
            int precision, exponent;
            String value;
            if (m.matches()) {
                precision = Integer.parseInt(m.group(2));
                exponent = Integer.parseInt(m.group(3));
                value = m.group(1);
            } else if (s.endsWith("f") || s.endsWith("F")) {
                precision = BinaryMathContext.BINARY32.precision;
                exponent = BinaryMathContext.BINARY32_EXPONENT_BITS;
                value = s.substring(0, s.length() - 1);
            } else {
                precision = BinaryMathContext.BINARY64.precision;
                exponent = BinaryMathContext.BINARY64_EXPONENT_BITS;
                if (s.endsWith("d") || s.endsWith("D")) {
                    value = s.substring(0, s.length() - 1);
                } else {
                    value = s;
                }
            }
            BinaryMathContext mc = new BinaryMathContext(precision, exponent);
            BigFloat result = new BigFloat(value, mc);
            return Pair.of(result, exponent);
        } catch (IllegalArgumentException e) {
            e.printStackTrace();
            throw new NumberFormatException();
        }
    }

    protected FloatBuiltin(Element element) {
        super(element);
        String s = element.getAttribute(Constants.VALUE_value_ATTR);
        Pair<BigFloat, Integer> pair = parseKFloat(s);
        if (pair == null) {
            throw KExceptionManager.criticalError(
                    s + " is not parseable as a valid Float.", this);
        }
        this.value = pair.getLeft();
        this.exponent = pair.getRight();
    }

    /**
     * Returns a {@link BigFloat} representing the (interpreted) value of the float token.
     */
    public BigFloat bigFloatValue() {
        return value;
    }

    /**
     * Returns a {@link BinaryMathContext} representing the context to perform arithmetic under.
     */
    public int exponent() {
        return exponent;
    }

    /**
     * Returns a {@link String} representing the sort name of a float token.
     */
    @Override
    public Sort tokenSort() {
        return Sort.BUILTIN_FLOAT;
    }

    /**
     * Returns a {@link String} representing the (uninterpreted) value of the float token.
     */
    @Override
    public String value() {
        return printKFloat(value) + printKFloatSuffix(value, exponent);
    }

    /**
     * Return a {@link String} representing the (uninterpreted) value of the numerical
     * float corresponding to the value of the float token.
     */
    public static String printKFloat(BigFloat value) {
        if (value.isInfinite()) {
            if (value.sign()) {
                return "-Infinity";
            } else {
                return "Infinity";
            }
        } else if (value.isNaN()) {
            return "NaN";
        } else {
            return value.toString();
        }
    }

    public static String printKFloatSuffix(BigFloat value, int exponent) {
        if (value.precision() == BinaryMathContext.BINARY64.precision
                && exponent == BinaryMathContext.BINARY64_EXPONENT_BITS) {
            return "";
        }
        if (value.precision() == BinaryMathContext.BINARY32.precision
                && exponent == BinaryMathContext.BINARY32_EXPONENT_BITS) {
            return "f";
        }
        return "p" + value.precision() + "x" + exponent;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

}
