package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Term;


/**
 * @author: AndreiS
 */
public class TermEquality {

    public static BoolToken eq(Term term1, Term term2) {
        checkArguments(term1, term2);
        return term1.equals(term2) ? BoolToken.TRUE : BoolToken.FALSE;
    }

    public static BoolToken ne(Term term1, Term term2) {
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

}
