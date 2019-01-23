// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;


/**
 * A boolean token. There are precisely two boolean values: "true" and "false".
 *
 * @author AndreiS
 */
public final class BoolToken extends Token {

    public static final Sort SORT = Sort.BOOL;

    /**
     * Bool(#"true")
     */
    public static final BoolToken TRUE = new BoolToken(true);

    /**
     * Bool("false")
     */
    public static final BoolToken FALSE = new BoolToken(false);

    /* boolean javaBackendValue wrapped by this BoolToken */
    private final boolean value;

    private BoolToken(boolean value) {
        this.value = value;
    }

    /**
     * Returns a {@code BoolToken} representation of the given {@code boolean} javaBackendValue.
     */
    public static BoolToken of(boolean value) {
        return value ? BoolToken.TRUE : BoolToken.FALSE;
    }

    /**
     * Returns a {@code boolean} representation of the (interpreted) javaBackendValue of this BoolToken.
     */
    public boolean booleanValue() {
        return value;
    }

    @Override
    public Sort sort() {
        return SORT;
    }

    /**
     * Returns a {@code String} representation of the (uninterpreted) javaBackendValue of this BoolToken.
     */
    @Override
    public String javaBackendValue() {
        return Boolean.toString(value);
    }

    @Override
    protected int computeHash() {
        return Boolean.valueOf(value).hashCode();
    }

    @Override
    public boolean equals(Object object) {
        return this == object;
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    /**
     * Returns the static instance rather than the de-serialized instance.
     */
    private Object readResolve() {
        return BoolToken.of(this.booleanValue());
    }

}
