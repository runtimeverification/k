package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

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

    /*
     * HashMap caches the constants to ensure uniqueness
     */
    private static Map<BigInteger, IntBuiltin> cache = new HashMap<BigInteger, IntBuiltin>();

    public static final IntBuiltin ZERO = IntBuiltin.of(0);
    public static final IntBuiltin ONE = IntBuiltin.of(1);

    public static IntBuiltin of(BigInteger value) {
        assert value != null : BigInteger.valueOf(0);
        IntBuiltin intBuiltin = cache.get(value);
        if (intBuiltin == null) {
            intBuiltin = new IntBuiltin(value);
            cache.put(value, intBuiltin);
        }
        return intBuiltin;
    }

    public static IntBuiltin of(long value) {
        return IntBuiltin.of(BigInteger.valueOf(value));
    }

    public static IntBuiltin of(String value) {
        return IntBuiltin.of(new BigInteger(value));
    }

    private final BigInteger value;

    private IntBuiltin(BigInteger value) {
        super(IntBuiltin.SORT_NAME);
        this.value = value;
    }

    public IntBuiltin(Element element) {
        super(element);
        value =  new BigInteger(element.getAttribute(Constants.VALUE_value_ATTR));
    }

    public BigInteger bigIntegerValue() {
        return value;
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
        if (this == object) {
            return true;
        }

        if (!(object instanceof IntBuiltin)) {
            return false;
        }

        IntBuiltin intBuiltin = (IntBuiltin) object;
        return value.equals(intBuiltin.value);
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
