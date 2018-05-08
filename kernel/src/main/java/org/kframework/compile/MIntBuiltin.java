// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.compile;

import org.apache.commons.lang3.tuple.Pair;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class MIntBuiltin {

    private static Map<Pair<BigInteger, Integer>, MIntBuiltin> tokenCache = new HashMap<>();

    public static MIntBuiltin of(BigInteger value, int precision) {
        assert value != null;
        Pair<BigInteger, Integer> key = Pair.of(value, precision);
        MIntBuiltin mintBuiltin = tokenCache.get(key);
        if (mintBuiltin == null) {
            mintBuiltin = new MIntBuiltin(value, precision);
            tokenCache.put(key, mintBuiltin);
        }
        return mintBuiltin;
    }

    public static MIntBuiltin of(String value) {
        Pair<BigInteger, Integer> pair = MIntBuiltin.parseKMInt(value);
        return of(pair.getLeft(), pair.getRight());
    }

    private final BigInteger value;
    private final int precision;

    private MIntBuiltin(BigInteger value, int precision) {
        this.value = value;
        this.precision = precision;
    }

    private static Pattern pattern = Pattern.compile("(\\d+*)[pP](\\d+)");
    public static Pair<BigInteger, Integer> parseKMInt(String s) {
        try {
            Matcher m = pattern.matcher(s);
            int precision;
            String value;
            if (m.matches()) {
                precision = Integer.parseInt(m.group(2));
                value = m.group(1);
            } else if (s.endsWith("i") || s.endsWith("I")) {
                precision = 32;
                value = s.substring(0, s.length() - 1);
            } else if (s.endsWith("l") || s.endsWith("L")) {
                precision = 64;
                value = s.substring(0, s.length() - 1);
            } else if (s.endsWith("s") || s.endsWith("S")) {
                precision = 16;
                value = s.substring(0, s.length() - 1);
            } else if (s.endsWith("b") || s.endsWith("B")) {
                precision = 8;
                value = s.substring(0, s.length() - 1);
            } else {
                throw new NumberFormatException();
            }
            BigInteger result = new BigInteger(value);
            return Pair.of(result, precision);
        } catch (IllegalArgumentException e) {
            e.printStackTrace();
            throw new NumberFormatException();
        }
    }

    public int precision() {
        return precision;
    }

    public BigInteger value() {
        return value;
    }
}
