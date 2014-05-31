// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 * A boolean token. There are precisely two boolean values: "true" and "false".
 *
 * @author AndreiS
 */
public final class BoolToken extends Token {

    public static final String SORT_NAME = "Bool";

    /**
     * Bool(#"true")
     */
    public static final BoolToken TRUE = new BoolToken(true);

    /**
     * Bool("false")
     */
    public static final BoolToken FALSE = new BoolToken(false);

    /* boolean value wrapped by this BoolToken */
    private final boolean value;

    private BoolToken(boolean value) {
        this.value = value;
    }

    /**
     * Returns a {@code BoolToken} representation of the given {@code boolean} value.
     */
    public static BoolToken of(boolean value) {
        return value ? BoolToken.TRUE : BoolToken.FALSE;
    }

    /**
     * Returns a {@code boolean} representation of the (interpreted) value of this BoolToken.
     */
    public boolean booleanValue() {
        return value;
    }

    /**
     * Returns a {@code String} representation of the sort of this BoolToken.
     */
    @Override
    public String sort() {
        return BoolToken.SORT_NAME;
    }

    /**
     * Returns a {@code String} representation of the (uninterpreted) value of this BoolToken.
     */
    @Override
    public String value() {
        return Boolean.toString(value);
    }

    @Override
    public int computeHash() {
        return Boolean.valueOf(value).hashCode();
    }

    @Override
    public boolean equals(Object object) {
        return this == object;
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }
    
    @Override
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
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
