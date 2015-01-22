// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import java.util.HashMap;
import java.util.Map;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.w3c.dom.Element;

/**
 * Class representing a builtin string token.
 *
 * Factory method {@link #of(String) StringBuiltin.of} expects a string representing the value
 * (an un-escaped string without the leading and trailing '"'). Method {@link #stringValue()
 * stringValue} returns the string value of the {@link StringBuiltin} token,
 * while method {@link #value() value} (declared in the superclass) returns the string
 * representation of the {@link StringBuiltin} token. For example,
 * the assertions in the following code are satisfied:
 *     StringBuiltin stringBuiltin = StringBuiltin.of("\"");
 *     assert stringBuiltin.stringValue().equals("\"");
 *     assert stringBuiltin.value().equals("\"\\\"\"") : stringBuiltin.value();
 */
public class StringBuiltin extends Token {

    /* Token cache */
    private static Map<String, StringBuiltin> tokenCache = new HashMap<String, StringBuiltin>();
    /* KApp cache */
    private static Map<String, KApp> kAppCache = new HashMap<String, KApp>();

    /**
     * #token("#String", " ")(.KList)
     */
    public static final KApp SPACE = StringBuiltin.kAppOf(" ");
    public static final KApp EMPTY = StringBuiltin.kAppOf("");

    /**
     * Returns a {@link StringBuiltin} representing the given {@link String} value.
     *
     * @param value An un-escaped {@link String} value without the leading and trailing '"'.
     * @return
     */
    public static StringBuiltin of(String value) {
        StringBuiltin stringBuiltin = tokenCache.get(value);
        if (stringBuiltin == null) {
            stringBuiltin = new StringBuiltin(value);
            tokenCache.put(value, stringBuiltin);
        }
        return stringBuiltin;
    }

    /**
     * Returns a {@link KApp} representing a {@link StringBuiltin} with the given (un-escaped)
     * value applied to an empty {@link KList}.
     *
     * @param value
     * @return
     */
    public static KApp kAppOf(String value) {
        KApp kApp = kAppCache.get(value);
        if (kApp == null) {
            kApp = KApp.of(StringBuiltin.of(value));
            kAppCache.put(value, kApp);
        }
        return kApp;
    }

    /**
     * Returns a {@link StringBuiltin} representing the value of a string textually represented by
     * the given {@link String} value.
     * @param value An escaped {@link String} value with the leading and trailing '"'.
     */
    public static StringBuiltin valueOf(String value) {
        assert value.charAt(0) == '"';
        assert value.charAt(value.length() - 1) == '"';
        String stringValue = StringUtil.unquoteKString(value);
        return StringBuiltin.of(stringValue);
    }

    /* un-escaped value of the string token */
    private final String value;

    private StringBuiltin(String value) {
        this.value = value;
    }

    private final String encodingErrorMsg = "The Unicode standard forbids the encoding of surrogate pair code points. If you need to perform operations on incorrectly-encoded strings, you must represent them as an array of code units.";

    protected StringBuiltin(Element element) {
        super(element);
        String s = element.getAttribute(Constants.VALUE_value_ATTR);
        try {
            value = StringUtil.unquoteKString(s);
        } catch (IllegalArgumentException e) {
            throw KExceptionManager.criticalError(encodingErrorMsg, e, this);
        }
    }

    /**
     * Returns a {@link String} representing the (interpreted) value of the string token.
     *
     * @return The un-escaped {@link String} value without the leading and trailing '"'.
     */
    public String stringValue() {
        return value;
    }

    /**
     * Returns a {@link String} representing the sort name of a string token.
     *
     * @return
     */
    @Override
    public Sort tokenSort() {
        return Sort.BUILTIN_STRING;
    }

    /**
     * Returns a {@link String} representing the (uninterpreted) value of the string token.
     *
     * @return The escaped {@link String} representation with the leading and trailing '"'.
     */
    @Override
    public String value() {
        return StringUtil.enquoteKString(value);
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }
}
