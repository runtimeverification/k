package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 * @author AndreiS
 */
public class BoolToken extends Token {

    public static final String SORT_NAME = "#Bool";

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
    public void accept(Matcher matcher, Term patten) {
        matcher.match(this, patten);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}
