// Copyright (c) K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.TruthValue;


/**
 * @author: AndreiS
 */
public class TermEquality {

    public static BoolToken eq(Term term1, Term term2, TermContext context) {
        if (hasKLabelVariables(term1) || hasKLabelVariables(term2)) {
            return null;
        }

        switch (getEqualityTruthValue(term1, term2, context)) {
            case TRUE:
                return BoolToken.TRUE;
            case FALSE:
                return BoolToken.FALSE;
            default:
                return null;
        }
    }

    public static BoolToken ne(Term term1, Term term2, TermContext context) {
        if (hasKLabelVariables(term1) || hasKLabelVariables(term2)) {
            return null;
        }

        switch (getEqualityTruthValue(term1, term2, context)) {
            case FALSE:
                return BoolToken.TRUE;
            case TRUE:
                return BoolToken.FALSE;
            default:
                return null;
        }
    }

    /**
     * Establishes the truth javaBackendValue of an equality between the two given terms by creating a
     * {@link org.kframework.backend.java.symbolic.ConjunctiveFormula} with one equality and
     * simplifying it.
     */
    private static TruthValue getEqualityTruthValue(Term term1, Term term2, TermContext context) {
        return ConjunctiveFormula.of(context.global()).add(term1, term2).simplify(context).truthValue();
    }

    private static boolean hasKLabelVariables(Term term) {
        for (Variable variable : term.variableSet()) {
            if (variable.kind() == Kind.KLABEL) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns the first or the second {@link Term} according to the javaBackendValue of
     * the {@link BoolToken}.
     *
     * @param boolToken
     *            the boolean token
     * @param t
     *            the first term
     * @param e
     *            the second term
     * @param context
     *            the term context
     * @return the first term if the {@code BoolToken} represents true;
     *         otherwise, the second term
     */
    public static Term ite(BoolToken boolToken, Term t, Term e, TermContext context) {
        if (boolToken.booleanValue()) return t;
        return e;
    }

}
