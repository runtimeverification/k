package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.w3c.dom.Element;

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

    /*
     * HashMap caches the constants to ensure uniqueness
     */
    private static Map<String, StringBuiltin> cache = new HashMap<String, StringBuiltin>();

    public static final StringBuiltin SPACE = StringBuiltin.of(" ");

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

    public StringBuiltin(Element element) {
        super(element);
        String s = element.getAttribute(Constants.VALUE_value_ATTR);
        value = s.substring(1, s.length() - 1);
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
        if (this == object) {
            return true;
        }

        if (!(object instanceof StringBuiltin)) {
            return false;
        }

        StringBuiltin stringBuiltin = (StringBuiltin) object;
        return value.equals(stringBuiltin.value);
    }

    @Override
    public String toString() {
        return "\"" + StringUtil.escape(getValue()) + "\"";
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
