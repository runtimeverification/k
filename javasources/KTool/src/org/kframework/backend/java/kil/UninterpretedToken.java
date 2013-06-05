package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.HashMap;
import java.util.Map;


/**
 * @author: AndreiS
 */
public class UninterpretedToken extends Token {

    /* Token cache */
    private static final Map<UninterpretedToken, UninterpretedToken> cache = new
            HashMap<UninterpretedToken, UninterpretedToken>();

    private final String sort;
    private final String value;

    private UninterpretedToken(String sort, String value) {
        this.sort = sort;
        this.value = value;
    }

    /**
     * Returns a {@code UninterpretedToken} representation of a token of given sort and value.
     */
    public static UninterpretedToken of(String sort, String value) {
        UninterpretedToken genericToken = new UninterpretedToken(sort, value);
        UninterpretedToken cachedGenericToken = cache.get(genericToken);
        if (cachedGenericToken == null) {
            cachedGenericToken = genericToken;
            cache.put(genericToken, cachedGenericToken);
        }
        return cachedGenericToken;
    }

    /**
     * Returns a {@code String} representation of the sort of this UninterpretedToken.
     */
    @Override
    public String sort() {
        return sort;
    }

    /**
     * Returns a {@code String} representation of the value of this UninterpretedToken.
     */
    @Override
    public String value() {
        return value;
    }

    @Override
    public boolean equals(Object object) {
        /* UninterpretedToken instances are cached */
        return this == object;
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
