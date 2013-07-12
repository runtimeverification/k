package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.utils.StringUtil;

import java.util.HashMap;
import java.util.Map;

/**
 * A string token. String tokens represent a sequence of unicode code points.
 In this regard they differ from the underlying String class they are built
 off of in Java because Java Strings are a sequence of 16-bit UTF-16
 characters.
 *
 * @author: DwightG
 */
public class StringToken extends Token {

    public static final String SORT_NAME = "String";

    /* StringToken cache */
    private static final Map<String, StringToken> cache = new HashMap<String, StringToken>();

    /* String value wrapped by this StringToken */
    private final String value;

    private StringToken(String value) {
        this.value = value;
    }

    /**
     * Returns a {@code StringToken} representation of a given {@link String}
     * value. The {@code StringToken} instances are cached to ensure uniqueness
     * (subsequent invocations of this method with the same {@code String}
     * value return the same {@code StringToken} object).
     * @param value A UTF-16 representation of this sequence of code points.
     */
    public static StringToken of(String value) {
        assert value != null;

        StringToken stringToken = cache.get(value);
        if (stringToken == null) {
            stringToken = new StringToken(value);
            cache.put(value, stringToken);
        }
        return stringToken;
    }

    /**
     * Returns a {@link String} representation of the interpreted value of
     * this StringToken.
     */
    public String stringValue() {
        return value;
    }

    /**
     * Returns a {@code String} representation of the sort of this StringToken.
     */
    public String sort() {
        return StringToken.SORT_NAME;
    }

    /**
     * Returns a {@code String} representation of the uninterpreted textual
     * value of this StringToken.
     */
    @Override
    public String value() {
        return StringUtil.escapeK(value);
    }

    @Override
    public int hashCode() {
        return value.hashCode();
    }

    @Override
    public boolean equals(Object object) {
        // cached
        return this == object;
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
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
