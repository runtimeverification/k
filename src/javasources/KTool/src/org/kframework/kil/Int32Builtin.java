// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.HashMap;
import java.util.Map;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

/**
 * Class representing a builtin integer token.
 */
public class Int32Builtin extends Token {

    public static final String SORT_NAME = "#Int32";

    /* Token cache */
    private static Map<Integer, Int32Builtin> tokenCache = new HashMap<Integer, Int32Builtin>();
    /* KApp cache */
    private static Map<Integer, KApp> kAppCache = new HashMap<Integer, KApp>();

    /**
     * #token("#Int", "0")(.KList)
     */
    public static final Int32Builtin ZERO_TOKEN = Int32Builtin.of(0);
    /**
     * #token("#Int", "1")(.KList)
     */
    public static final Int32Builtin ONE_TOKEN = Int32Builtin.of(1);

    /**
     * #token("#Int", "0")(.KList)
     */
    public static final KApp ZERO = Int32Builtin.kAppOf(0);
    /**
     * #token("#Int", "1")(.KList)
     */
    public static final KApp ONE = Int32Builtin.kAppOf(1);

    /**
     * Returns a {@link Int32Builtin} representing the given {@link Integer} value.
     * 
     * @param value
     * @return
     */
    public static Int32Builtin of(int value) {

        Int32Builtin intBuiltin = tokenCache.get(value);
        if (intBuiltin == null) {
            intBuiltin = new Int32Builtin(value);
            tokenCache.put(value, intBuiltin);
        }
        return intBuiltin;
    }

    /**
     * Returns a {@link Int32Builtin} representing a {@link Integer} with the given {@link String} representation.
     * 
     * @param value
     * @return
     */
    public static Int32Builtin of(String value) {
        assert value != null;

        return Int32Builtin.of(new Integer(value));
    }

    /**
     * Returns a {@link KApp} representing a {@link Int32Builtin} with the given value applied to an empty {@link KList}.
     * 
     * @param value
     * @return
     */
    public static KApp kAppOf(int value) {

        KApp kApp = kAppCache.get(value);
        if (kApp == null) {
            kApp = KApp.of(Int32Builtin.of(value));
            kAppCache.put(value, kApp);
        }
        return kApp;
    }

    /**
     * Returns a {@link KApp} representing a {@link Int32Builtin} with the given value applied to an empty {@link KList}.
     * 
     * @param value
     * @return
     */
    public static KApp kAppOf(long value) {
        return Int32Builtin.kAppOf((int) value);
    }

    /**
     * Returns a {@link KApp} representing a {@link Int32Builtin} with the given {@link String} representation applied to an empty {@link KList}.
     * 
     * @param value
     * @return
     */
    public static KApp kAppOf(String value) {
        assert value != null;

        return Int32Builtin.kAppOf(new Integer(value));
    }

    private final int value;

    private Int32Builtin(int value) {
        this.value = value;
    }

    protected Int32Builtin(Element element) {
        super(element);
        value = new Integer(element.getAttribute(Constants.VALUE_value_ATTR));
    }

    /**
     * Returns a {@link Integer} representing the (interpreted) value of the int token.
     */
    public int intValue() {
        return value;
    }

    /**
     * Returns a {@link String} representing the sort name of a int token.
     */
    @Override
    public String tokenSort() {
        return Int32Builtin.SORT_NAME;
    }

    /**
     * Returns a {@link String} representing the (uninterpreted) value of the int token.
     */
    @Override
    public String value() {
        return Integer.toString(value);
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
}
