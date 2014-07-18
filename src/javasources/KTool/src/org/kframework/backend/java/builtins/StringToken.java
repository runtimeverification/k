// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.MaximalSharing;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.utils.StringUtil;

import java.io.UnsupportedEncodingException;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.Charset;
import java.nio.charset.CodingErrorAction;
import java.util.HashMap;
import java.util.Map;

/**
 * A string token. String tokens represent a sequence of unicode code points.
 * In this regard they differ from the underlying String class they are built
 * off of in Java because Java Strings are a sequence of 16-bit UTF-16 characters.
 *
 * @author DwightG
 */
public final class StringToken extends Token implements MaximalSharing {

    public static final Sort SORT = Sort.STRING;

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
     * Returns a {@code StringToklen} representation of a given {@code byte[]} value. This value is
     * interpreted as a sequence of code points in the Latin-1 Unicode block according to the
     * ISO-8859-1 encoding.
     * @param value A Latin-1 representation of the sequence of code points.
     */
    public static StringToken of(byte[] value) {
        try {
            String stringValue = new String(value, "ISO-8859-1");
            return of(stringValue);
        } catch (UnsupportedEncodingException e) {
            throw new AssertionError("no latin-1 charset???");
        }
    }

    /**
     * Returns a {@link String} representation of the interpreted value of
     * this StringToken.
     */
    public String stringValue() {
        return value;
    }

    /**
     * Returns a {@code byte[]} representation of the interpreted value of this StringToken.
     * @throws CharacterCodingException Thrown if the String is not a valid sequence of code points
     * in the 0-255 range.
     */
    public byte[] byteArrayValue() throws CharacterCodingException {
        ByteBuffer buffer = Charset.forName("ISO-8859-1")
            .newEncoder()
            .onUnmappableCharacter(CodingErrorAction.REPORT)
            .encode(CharBuffer.wrap(value));
        byte[] bytes = new byte[buffer.remaining()];
        buffer.get(bytes);
        return bytes;
    }

    public Sort sort() {
        return SORT;
    }

    /**
     * Returns a {@code String} representation of the uninterpreted textual
     * value of this StringToken.
     */
    @Override
    public String value() {
        return StringUtil.enquoteString(value);
    }

    @Override
    protected int computeHash() {
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
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    /**
     * Returns the cached instance rather than the de-serialized instance if there is a cached
     * instance.
     */
    private Object readResolve() {
        StringToken stringToken = cache.get(value);
        if (stringToken == null) {
            stringToken = this;
            cache.put(value, stringToken);
        }
        return stringToken;
    }

}
