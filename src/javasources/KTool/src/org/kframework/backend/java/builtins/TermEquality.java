package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

/**
 * @author: AndreiS
 */
public class TermEquality {

    public static BoolToken eq(Term term1, Term term2, TermContext context) {
        checkArguments(term1, term2);
        return term1.equals(term2) ? BoolToken.TRUE : BoolToken.FALSE;
    }

    public static BoolToken ne(Term term1, Term term2, TermContext context) {
        checkArguments(term1, term2);
        return term1.equals(term2) ? BoolToken.FALSE : BoolToken.TRUE;
    }
    
    private static void checkArguments(Term term1, Term term2) {
        if (!term1.isGround()) {
            throw new IllegalArgumentException("first argument " + term1 + " is not ground");
        }
        if (!term2.isGround()) {
            throw new IllegalArgumentException("second argument " + term2 + " is not ground");
        }
    }

    /**
     * Returns the first or the second {@link Term} according to the value of
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
