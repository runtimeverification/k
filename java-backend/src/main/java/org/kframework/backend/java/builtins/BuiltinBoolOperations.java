// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;


import org.kframework.backend.java.kil.Term;
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

    public static Term andThen(Term term1, Term term2, TermContext context) {
        if (term1 instanceof BoolToken) {
            BoolToken boolToken1 = (BoolToken) term1;
            return boolToken1.booleanValue() ? term2 : BoolToken.FALSE;
        } else if (term2 instanceof BoolToken) {
            BoolToken boolToken2 = (BoolToken) term2;
            return boolToken2.booleanValue() ? term1 : BoolToken.FALSE;
        } else {
            return null;
        }
    }

    public static BoolToken or(BoolToken term1, BoolToken term2, TermContext context) {
        return BoolToken.of(term1.booleanValue() || term2.booleanValue());
    }

    public static Term orElse(Term term1, Term term2, TermContext context) {
        if (term1 instanceof BoolToken) {
            BoolToken boolToken1 = (BoolToken) term1;
            return boolToken1.booleanValue() ? BoolToken.TRUE : term2;
        } else if (term2 instanceof BoolToken) {
            BoolToken boolToken2 = (BoolToken) term2;
            return boolToken2.booleanValue() ? BoolToken.TRUE : term1;
        } else {
            return null;
        }
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
