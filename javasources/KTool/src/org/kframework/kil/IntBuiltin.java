package org.kframework.kil;

import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.math.BigInteger;

import java.util.HashMap;
import java.util.Map;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 4/17/13
 * Time: 12:21 PM
 * To change this template use File | Settings | File Templates.
 */
public class IntBuiltin extends Builtin {

    public static final String SORT_NAME = "#Int";

    public static final IntBuiltin ZERO = IntBuiltin.of("0");
    public static final IntBuiltin ONE = IntBuiltin.of("1");

    /*
     * HashMap caches the constants to ensure uniqueness
     */
    private static Map<BigInteger, IntBuiltin> cache = new HashMap<BigInteger, IntBuiltin>();

    public static IntBuiltin of(String value) {
        BigInteger bigInteger = new BigInteger(value);
        IntBuiltin intBuiltin = cache.get(bigInteger);
        if (intBuiltin == null) {
            intBuiltin = new IntBuiltin(bigInteger);
            cache.put(bigInteger, intBuiltin);
        }
        return intBuiltin;
    }

    private final BigInteger value;

    private IntBuiltin(BigInteger value) {
        super(IntBuiltin.SORT_NAME);
        this.value = value;
    }

    @Override
    public String getValue() {
        return value.toString();
    }

    @Override
    public Term shallowCopy() {
        /* this object is immutable */
        return this;
    }

    @Override
    public int hashCode() {
        return value.hashCode();
    }

    @Override
    public boolean equals(Object object) {
        /* the cache ensures uniqueness of logically equal object instances */
        return this == object;
    }

    @Override
    public String toString() {
        return getValue();
    }

    @Override
    public void accept(Matcher matcher, Term toMatch) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}
