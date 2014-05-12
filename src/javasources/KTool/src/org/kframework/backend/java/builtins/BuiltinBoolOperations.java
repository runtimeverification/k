// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;


import org.kframework.backend.java.kil.TermContext;

/**
 * Table of {@code public static} methods on builtin boolean values.
 *
 * @author: AndreiS
 */
public class BuiltinBoolOperations {

    public static BoolToken not(BoolToken term, TermContext context) {
        return BoolToken.of(!term.booleanValue());
    }

    public static BoolToken and(BoolToken term1, BoolToken term2, TermContext context) {
        return BoolToken.of(term1.booleanValue() && term2.booleanValue());
    }

    public static BoolToken or(BoolToken term1, BoolToken term2, TermContext context) {
        return BoolToken.of(term1.booleanValue() || term2.booleanValue());
    }

    public static BoolToken xor(BoolToken term1, BoolToken term2, TermContext context) {
        return BoolToken.of(term1.booleanValue() ^ term2.booleanValue());
    }

    public static BoolToken implies(BoolToken term1, BoolToken term2, TermContext context) {
        return BoolToken.of(!term1.booleanValue() || term2.booleanValue());
    }

    public static BoolToken eq(BoolToken term1, BoolToken term2, TermContext context) {
        return BoolToken.of(term1.booleanValue() == term2.booleanValue());
    }

    public static BoolToken ne(BoolToken term1, BoolToken term2, TermContext context) {
        return BoolToken.of(term1.booleanValue() != term2.booleanValue());
    }

}
