// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

/**
 * Class representing a builtin integer token.
 */
public class IntBuiltin extends Token {

    /* Token cache */
    private static Map<BigInteger, IntBuiltin> tokenCache = new HashMap<BigInteger, IntBuiltin>();
    /* KApp cache */
    private static Map<BigInteger, KApp> kAppCache = new HashMap<BigInteger, KApp>();

    /**
     * #token("#Int", "0")(.KList)
     */
    public static final IntBuiltin ZERO_TOKEN = IntBuiltin.of(0);
    /**
     * #token("#Int", "1")(.KList)
     */
    public static final IntBuiltin ONE_TOKEN = IntBuiltin.of(1);

    /**
     * #token("#Int", "0")(.KList)
     */
    public static final KApp ZERO = IntBuiltin.kAppOf(0);
    /**
     * #token("#Int", "1")(.KList)
     */
    public static final KApp ONE = IntBuiltin.kAppOf(1);

    /**
     * Returns a {@link IntBuiltin} representing the given {@link BigInteger} value.
     *
     * @param value
     * @return
     */
    public static IntBuiltin of(BigInteger value) {
        assert value != null;

        IntBuiltin intBuiltin = tokenCache.get(value);
        if (intBuiltin == null) {
            intBuiltin = new IntBuiltin(value);
            tokenCache.put(value, intBuiltin);
        }
        return intBuiltin;
    }

    /**
     * Returns a {@link IntBuiltin} representing the given {@link long} value.
     *
     * @param value
     * @return
     */
    public static IntBuiltin of(long value) {
        return IntBuiltin.of(BigInteger.valueOf(value));
    }

    /**
     * Returns a {@link IntBuiltin} representing a {@link BigInteger} with the given {@link String} representation.
     *
     * @param value
     * @return
     */
    public static IntBuiltin of(String value) {
        assert value != null;

        return IntBuiltin.of(new BigInteger(value));
    }

    /**
     * Returns a {@link KApp} representing a {@link IntBuiltin} with the given value applied to an empty {@link KList}.
     *
     * @param value
     * @return
     */
    public static KApp kAppOf(BigInteger value) {
        assert value != null;

        KApp kApp = kAppCache.get(value);
        if (kApp == null) {
            kApp = KApp.of(IntBuiltin.of(value));
            kAppCache.put(value, kApp);
        }
        return kApp;
    }

    /**
     * Returns a {@link KApp} representing a {@link IntBuiltin} with the given value applied to an empty {@link KList}.
     *
     * @param value
     * @return
     */
    public static KApp kAppOf(long value) {
        return IntBuiltin.kAppOf(BigInteger.valueOf(value));
    }

    /**
     * Returns a {@link KApp} representing a {@link IntBuiltin} with the given {@link String} representation applied to an empty {@link KList}.
     *
     * @param value
     * @return
     */
    public static KApp kAppOf(String value) {
        assert value != null;

        return IntBuiltin.kAppOf(new BigInteger(value));
    }

    private final BigInteger value;

    private IntBuiltin(BigInteger value) {
        this.value = value;
    }

    protected IntBuiltin(Element element) {
        super(element);
        value = new BigInteger(element.getAttribute(Constants.VALUE_value_ATTR));
    }

    /**
     * Returns a {@link BigInteger} representing the (interpreted) value of the int token.
     */
    public BigInteger bigIntegerValue() {
        return value;
    }

    @Override
    public Sort tokenSort() {
        return Sort.BUILTIN_INT;
    }

    /**
     * Returns a {@link String} representing the (uninterpreted) value of the int token.
     */
    @Override
    public String value() {
        return value.toString();
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
}
