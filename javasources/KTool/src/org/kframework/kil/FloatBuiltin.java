package org.kframework.kil;

import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.HashMap;
import java.util.Map;

/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 4/17/13
 * Time: 12:22 PM
 * To change this template use File | Settings | File Templates.
 */
public class FloatBuiltin extends Builtin {

    public static final String SORT_NAME = "#Float";

    public static final FloatBuiltin ZERO = FloatBuiltin.of("0");

    /*
     * HashMap caches the constants to ensure uniqueness
     */
    private static Map<Double, FloatBuiltin> cache = new HashMap<Double, FloatBuiltin>();

    public static FloatBuiltin of(String value) {
        Double d = Double.valueOf(value);
        FloatBuiltin floatBuiltin = cache.get(d);
        if (floatBuiltin == null) {
            floatBuiltin = new FloatBuiltin(d);
            cache.put(d, floatBuiltin);
        }
        return floatBuiltin;
    }

    private final Double value;

    private FloatBuiltin(Double value) {
        super(FloatBuiltin.SORT_NAME);
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
