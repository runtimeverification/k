package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;


/**
 * @author: AndreiS
 */
public class IntToken extends Token {

    public static final String SORT_NAME = "#Int";

    /* IntToken cache */
    private static final Map<BigInteger, IntToken> cache = new HashMap<BigInteger, IntToken>();

    /* BigInteger value wrapped by this IntToken */
    private final BigInteger value;

    private IntToken(BigInteger value) {
        this.value = value;
    }

    /**
     * Returns a {@code IntToken} representation of the given {@link BigInteger} value. The
     * IntToken instances are cached to ensure uniqueness (subsequent invocations of this method
     * with the same {@code BigInteger} value return the same IntToken object).
     */
    public static IntToken of(BigInteger value) {
        assert value != null;

        IntToken intToken = cache.get(value);
        if (intToken == null) {
            intToken = new IntToken(value);
            cache.put(value, intToken);
        }
        return intToken;
    }

    /**
     * Returns a {@link BigInteger} representation of the (interpreted) value of this IntToken.
     */
    public BigInteger bigIntegerValue() {
        return value;
    }

    /**
     * Returns a {@code String} representation of the sort of this IntToken.
     */
    @Override
    public String sort() {
        return IntToken.SORT_NAME;
    }

    /**
     * Returns a {@code String} representation of the (uninterpreted) value of this IntToken.
     */
    @Override
    public String value() {
        return value.toString();
    }

    @Override
    public int hashCode() {
        return value.hashCode();
    }

    @Override
    public boolean equals(Object object) {
        /* IntToken instances are cached */
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
