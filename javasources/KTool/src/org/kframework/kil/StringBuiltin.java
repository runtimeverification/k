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
public class StringBuiltin extends Builtin {

    public static final String SORT_NAME = "#String";

    public static final StringBuiltin SPACE = StringBuiltin.of(" ");

    /*
     * HashMap caches the constants to ensure uniqueness
     */
    private static Map<String, StringBuiltin> cache = new HashMap<String, StringBuiltin>();

    public static StringBuiltin of(String value) {
        StringBuiltin stringBuiltin = cache.get(value);
        if (stringBuiltin == null) {
            stringBuiltin = new StringBuiltin(value);
            cache.put(value, stringBuiltin);
        }
        return stringBuiltin;
    }

    private final String value;

    private StringBuiltin(String value) {
        super(StringBuiltin.SORT_NAME);
        this.value = value;
    }

    @Override
    public String getValue() {
        return value;
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
        return "\"" + getValue() + "\"";
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
