package org.kframework.kore.compile;

import org.kframework.kore.KRewrite;

/**
 * A visitor designed to track whether we are currently in the left hand side or right hand side of a term.
 *
 * This visitor provides two boolean methods, isRHS() and isLHS(). Outside of a rewrite, both are true, signifying
 * that the term being visited is part of both the LHS and the RHS. Inside a rewrite, only one is true. It is an error
 * for both to be false.
 */
public class RewriteAwareVisitor extends VisitKORE {

    private boolean isRHS = true;
    private boolean isLHS = true;

    public boolean isLHS() {
        return isLHS;
    }

    public boolean isRHS() {
        return isRHS;
    }

    @Override
    public Void apply(KRewrite k) {
        isRHS = false;
        apply(k.left());
        isRHS = true;
        isLHS = false;
        apply(k.right());
        isLHS = true;
        return null;
    }
}
