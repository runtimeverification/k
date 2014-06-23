// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import java.math.BigInteger;

import org.apache.commons.lang3.StringUtils;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kil.FloatBuiltin;
import org.kframework.backend.java.kil.Token;
import org.kframework.utils.StringUtil;

/**
 * Table of {@code public static} methods on builtin strings.
 *
 * @author: DwightG
 */

public class BuiltinStringOperations {

    public static StringToken add(StringToken term1, StringToken term2, TermContext context) {
        return StringToken.of(term1.stringValue() + term2.stringValue());
    }

    public static BoolToken eq(StringToken term1, StringToken term2, TermContext context) {
        return BoolToken.of(term1.stringValue().compareTo(term2.stringValue()) == 0);
    }

    public static BoolToken ne(StringToken term1, StringToken term2, TermContext context) {
        return BoolToken.of(term1.stringValue().compareTo(term2.stringValue()) != 0);
    }

    public static BoolToken gt(StringToken term1, StringToken term2, TermContext context) {
        return BoolToken.of(term1.stringValue().compareTo(term2.stringValue()) > 0);
    }

    public static BoolToken ge(StringToken term1, StringToken term2, TermContext context) {
        return BoolToken.of(term1.stringValue().compareTo(term2.stringValue()) >= 0);
    }

    public static BoolToken lt(StringToken term1, StringToken term2, TermContext context) {
        return BoolToken.of(term1.stringValue().compareTo(term2.stringValue()) < 0);
    }

    public static BoolToken le(StringToken term1, StringToken term2, TermContext context) {
        return BoolToken.of(term1.stringValue().compareTo(term2.stringValue()) <= 0);
    }

    public static IntToken len(StringToken term, TermContext context) {
        return IntToken.of(term.stringValue().codePointCount(0, term.stringValue().length()));
    }

    public static IntToken ord(StringToken term, TermContext context) {
        if (term.stringValue().codePointCount(0, term.stringValue().length()) != 1) {
            throw new IllegalArgumentException();
        }
        return IntToken.of(term.stringValue().codePointAt(0));
    }

    public static StringToken chr(IntToken term, TermContext context) {
        //safe because we know it's in the unicode code range or it will throw
        int codePoint = term.intValue();
        StringUtil.throwIfSurrogatePair(codePoint);
        char[] chars = Character.toChars(codePoint);
        return StringToken.of(new String(chars));
    }

    public static StringToken substr(StringToken term, IntToken start, IntToken end, TermContext context) {
        int beginOffset = term.stringValue().offsetByCodePoints(0, start.intValue());
        int endOffset = term.stringValue().offsetByCodePoints(0, end.intValue());
        return StringToken.of(term.stringValue().substring(beginOffset, endOffset));
    }

    public static IntToken find(StringToken term1, StringToken term2, IntToken idx, TermContext context) {
        int offset = term1.stringValue().offsetByCodePoints(0, idx.intValue());
        int foundOffset = term1.stringValue().indexOf(term2.stringValue(), offset);
        return IntToken.of((foundOffset == -1 ? -1 : term1.stringValue().codePointCount(0, foundOffset)));
    }

    public static IntToken rfind(StringToken term1, StringToken term2, IntToken idx, TermContext context) {
        int offset = term1.stringValue().offsetByCodePoints(0, idx.intValue());
        int foundOffset = term1.stringValue().lastIndexOf(term2.stringValue(), offset);
        return IntToken.of((foundOffset == -1 ? -1 : term1.stringValue().codePointCount(0, foundOffset)));
    }

    public static IntToken findChar(StringToken term1, StringToken term2, IntToken idx, TermContext context) {
        int offset = term1.stringValue().offsetByCodePoints(0, idx.intValue());
        int foundOffset = StringUtil.indexOfAny(term1.stringValue(), term2.stringValue(), offset);
        return IntToken.of((foundOffset == -1 ? -1 : term1.stringValue().codePointCount(0, foundOffset)));
    }

    public static IntToken rfindChar(StringToken term1, StringToken term2, IntToken idx, TermContext context) {
        int offset = term1.stringValue().offsetByCodePoints(0, idx.intValue());
        int foundOffset = StringUtil.lastIndexOfAny(term1.stringValue(), term2.stringValue(), offset);
        return IntToken.of((foundOffset == -1 ? -1 : term1.stringValue().codePointCount(0, foundOffset)));
    }

    public static IntToken string2int(StringToken term, TermContext context) {
        return IntToken.of(term.stringValue());
    }

    public static IntToken string2base(StringToken term, IntToken base, TermContext context) {
        return IntToken.of(new BigInteger(term.stringValue(), base.intValue()));
    }
    
    public static StringToken base2string(IntToken integer, IntToken base, TermContext context) {
        return StringToken.of(integer.bigIntegerValue().toString(base.intValue()));
    }

    public static FloatToken string2float(StringToken term, TermContext context) {
        try {
            return FloatToken.of(term.stringValue());
        } catch (NumberFormatException e) {
            return null;
        }
    }

    public static StringToken float2string(FloatToken term, TermContext context) {
        return StringToken.of(FloatBuiltin.printKFloat(term.bigFloatValue()));
    }

    public static StringToken int2string(IntToken term, TermContext context) {
        return StringToken.of(term.bigIntegerValue().toString());
    }
/*
    // when we support java 7
    public static StringToken name(StringToken term) {
        if (term.stringValue().codePointCount(0, term.stringValue().length()) != 1) {
            throw new IllegalArgumentException();
        }
        String name = Character.getName(term.stringValue().codePointAt(0));
        if (name == null) {
            throw new IllegalArgumentExceptino();
        }
        return StringToken.of(name);
    }
*/
    public static StringToken category(StringToken term, TermContext context) {
        if (term.stringValue().codePointCount(0, term.stringValue().length()) != 1) {
            throw new IllegalArgumentException();
        }
        int cat = Character.getType(term.stringValue().codePointAt(0));
        assert cat >= 0 && cat < 128 : "not a byte???";
        return StringToken.of(StringUtil.getCategoryCode((byte)cat));
    }

    public static StringToken directionality(StringToken term, TermContext context) {
        if (term.stringValue().codePointCount(0, term.stringValue().length()) != 1) {
            throw new IllegalArgumentException();
        }
        byte cat = Character.getDirectionality(term.stringValue().codePointAt(0));
        return StringToken.of(StringUtil.getDirectionalityCode(cat));
    }

    public static StringToken token2string(UninterpretedToken token, TermContext context) {
        return StringToken.of(token.value());
    }

    public static Token string2token(StringToken sort, StringToken value, TermContext context) {
        return Token.of(sort.stringValue(), value.stringValue());
    }
    
    /**
     * Replaces all occurrences of a string within another string.
     * 
     * @param text
     *            the string to search and replace in
     * @param search
     *            the string to search for
     * @param replacement
     *            the string to replace it with
     * @param context
     *            the term context
     * @return the text with any replacements processed
     */
    public static StringToken replaceAll(StringToken text,
            StringToken searchString, StringToken replacement,
            TermContext context) {
        return StringToken.of(StringUtils.replace(text.stringValue(),
                searchString.stringValue(), replacement.stringValue()));
    }
    
    /**
     * Replaces all occurrences of a string within another string, for the first
     * max values of the search string.
     * 
     * @param text
     *            the string to search and replace in
     * @param search
     *            the string to search for
     * @param replacement
     *            the string to replace it with
     * @param max
     *            the maximum number of occurrences to be replaced
     * @param context
     *            the term context
     * @return the text with any replacements processed
     */
    public static StringToken replace(StringToken text,
            StringToken searchString, StringToken replacement, IntToken max,
            TermContext context) {
        return StringToken.of(StringUtils.replace(text.stringValue(),
                searchString.stringValue(), replacement.stringValue(),
                max.intValue()));
    }
    
    /**
     * Replaces the first occurrence of a string within another string.
     * 
     * @param text
     *            the string to search and replace in
     * @param search
     *            the string to search for
     * @param replacement
     *            the string to replace it with
     * @param context
     *            the term context
     * @return the text with any replacements processed
     */
    public static StringToken replaceFirst(StringToken text,
            StringToken searchString, StringToken replacement,
            TermContext context) {
        return StringToken.of(StringUtils.replaceOnce(text.stringValue(),
                searchString.stringValue(), replacement.stringValue()));
    }
    
    /**
     * Counts how many times the substring appears in another string.
     * 
     * @param text
     *            the string to search in
     * @param substr
     *            the substring to search for
     * @param context
     *            the term context
     * @return the number of occurrences
     */
    public static IntToken countOccurences(StringToken text,
            StringToken substr, TermContext context) {
        return IntToken.of(StringUtils.countMatches(text.stringValue(),
                substr.stringValue()));
    }
}
