package org.kframework.kil;

import org.apache.commons.lang3.StringEscapeUtils;
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
 * Class representing a builtin string token. Factory method {@link #of(String)
 * StringBuiltin.of} expects a string representing the value (an un-escaped string without the
 * leading and trailing '"'). Method {@link #stringValue() stringValue} returns the string value
 * of the {@link StringBuiltin} token, while method {@link #value() value} (declared in the
 * superclass) returns the string representation of the {@link StringBuiltin} token. For example,
 * the assertions in the following code are satisfied:
 *     StringBuiltin stringBuiltin = StringBuiltin.of("\"");
 *     assert stringBuiltin.stringValue().equals("\"");
 *     assert stringBuiltin.value().equals("\"\\\"\"") : stringBuiltin.value();
 */
public class StringBuiltin extends Token {

    public static final String SORT_NAME = "#String";

    /* Token cache */
    private static Map<String, StringBuiltin> tokenCache = new HashMap<String, StringBuiltin>();
    /* KApp cache */
    private static Map<String, KApp> kAppCache = new HashMap<String, KApp>();

    /**
     * #token("#String", " ")(.KList)
     */
    public static final KApp SPACE = StringBuiltin.kAppOf(" ");

    /**
     * Returns a {@link StringBuiltin} representing the given {@link String} value.
     * @param value An un-escaped {@link String} value without the leading and trailing '"'.
     * @return
     */
    public static StringBuiltin of(String value) {
        StringBuiltin stringBuiltin = tokenCache.get(value);
        if (stringBuiltin == null) {
            stringBuiltin = new StringBuiltin(value);
            tokenCache.put(value, stringBuiltin);
        }
        return stringBuiltin;
    }

    /**
     * Returns a {@link KApp} representing a {@link StringBuiltin} with the given (un-escaped)
     * value applied to an empty {@link KList}.
     * @param value
     * @return
     */
    public static KApp kAppOf(String value) {
        KApp kApp = kAppCache.get(value);
        if (kApp == null) {
            kApp = KApp.of(StringBuiltin.of(value));
            kAppCache.put(value, kApp);
        }
        return kApp;
    }

    /* un-escaped value of the string token */
    private final String value;

    private StringBuiltin(String value) {
        this.value = value;
    }

    protected StringBuiltin(Element element) {
        super(element);
        String s = element.getAttribute(Constants.VALUE_value_ATTR);
        value = StringEscapeUtils.unescapeJava(s.substring(1, s.length() - 1));
    }

    /**
     * Returns a {@link String} representing the (interpreted) value of the string token.
     * @return The un-escaped {@link String} value without the leading and trailing '"'.
     */
    public String stringValue() {
        return value;
    }

    /**
     * Returns a {@link String} representing the sort name of a string token.
     * @return
     */
    @Override
    public String tokenSort() {
        return StringBuiltin.SORT_NAME;
    }

    /**
     * Returns a {@link String} representing the (uninterpreted) value of the string token.
     * @return The escaped {@link String} representation with the leading and trailing '"'.
     */
    @Override
    public String value() {
        /* TODO: andreis to see what maude supports and convert accordingly */
        return ("\"" + StringEscapeUtils.escapeJava(value) + "\"").replaceAll("\\\\u0", "\\\\");
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
