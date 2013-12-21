package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.TermFormulaPair;
import org.kframework.backend.java.symbolic.UninterpretedConstraint;

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
    
    /**
     * Experimental implementation of semantic equality.
     * 
     * @param term1
     * @param term2
     * @param context
     * @return
     */
    public static TermFormulaPair semeq(Term term1, Term term2, TermContext context) {
        UninterpretedConstraint uninterpretedCnstr = new UninterpretedConstraint();
        uninterpretedCnstr.add(term1, term2);
        return new TermFormulaPair(BoolToken.TRUE, uninterpretedCnstr);
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
