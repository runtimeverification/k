// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

/**
 * Class representing a builtin boolean token.
 */
public class BoolBuiltin extends Token {

    public static final String TRUE_STRING = "true";
    public static final String FALSE_STRING = "false";

    /**
     * #token("#Bool", "true")
     */
    public static final BoolBuiltin TRUE_TOKEN = new BoolBuiltin(Boolean.TRUE);
    /**
     * #token("#Bool", "false")
     */
    public static final BoolBuiltin FALSE_TOKEN = new BoolBuiltin(Boolean.FALSE);

    /**
     * #token("#Bool", "true")(.KList)
     */
    public static final KApp TRUE = KApp.of(BoolBuiltin.TRUE_TOKEN);
    /**
     * #token("#Bool", "false")(.KList)
     */
    public static final KApp FALSE = KApp.of(BoolBuiltin.FALSE_TOKEN);

    /**
     * Returns a {@link BoolBuiltin} representing a {@link boolean} value with the given {@link String} representation.
     *
     * @param value
     * @return
     */
    public static BoolBuiltin of(String value) {
        checkValue(value);

        if (value.equals(BoolBuiltin.TRUE_STRING)) {
            return BoolBuiltin.TRUE_TOKEN;
        } else {
            return BoolBuiltin.FALSE_TOKEN;
        }
    }

    /**
     * Returns a {@link KApp} representing a {@link BoolBuiltin} with the given value applied to an empty {@link KList}.
     *
     * @param value
     * @return
     */
    public static KApp kAppOf(String value) {
        checkValue(value);

        if (value.equals(BoolBuiltin.TRUE_STRING)) {
            return BoolBuiltin.TRUE;
        } else {
            return BoolBuiltin.FALSE;
        }
    }

    private static void checkValue(String value) {
        assert value.equals(BoolBuiltin.TRUE_STRING) || value.equals(BoolBuiltin.FALSE_STRING) : "unexpected value " + value + " for a builtin bool token; expected one of "
                + BoolBuiltin.TRUE_STRING + " or " + BoolBuiltin.FALSE_STRING;
    }

    private final Boolean value;

    private BoolBuiltin(Boolean value) {
        this.value = value;
    }

    protected BoolBuiltin(Element element) {
        super(element);
        String s = element.getAttribute(Constants.VALUE_value_ATTR);

        checkValue(s);

        value = Boolean.valueOf(s);
    }

    /**
     * Returns a {@link Boolean} representing the (interpreted) value of the boolean token.
     */
    public Boolean booleanValue() {
        return value;
    }

    /**
     * Returns a {@link String} representing the sort name of a boolean token.
     *
     * @return
     */
    @Override
    public Sort tokenSort() {
        return Sort.BUILTIN_BOOL;
    }

    /**
     * Returns a {@link String} representing the (uninterpreted) value of the boolean token.
     *
     * @return
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
