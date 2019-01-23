// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.kore.KApply;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;

/**
 * A visitor designed to track whether we are currently in the left hand side or right hand side of a term.
 *
 * This visitor provides two boolean methods, isRHS() and isLHS(). Outside of a rewrite, both are true, signifying
 * that the term being visited is part of both the LHS and the RHS. Inside a rewrite, only one is true. It is an error
 * for both to be false.
 */
public class RewriteAwareVisitor extends VisitK {

    private final Set<KEMException> errors;
    public RewriteAwareVisitor(boolean isBody, Set<KEMException> errors) {
        this.errors = errors;
        if (isBody) {
            isRHS = true;
            isLHS = true;
        } else {
            isRHS = true;
            isLHS = false;
        }
    }


    private boolean isRHS;
    private boolean isLHS;

    public boolean isLHS() {
        return isLHS;
    }

    public boolean isRHS() {
        return isRHS;
    }

    @Override
    public void apply(KRewrite k) {
        isRHS = false;
        apply(k.left());
        isRHS = true;
        isLHS = false;
        apply(k.right());
        isLHS = true;
    }

    @Override
    public void apply(KApply k) {
        if (!(k.klabel() instanceof KVariable) && k.klabel().name().equals("#fun2") || k.klabel().name().equals("#fun3")) {
            boolean wasRHS = isRHS;
            boolean wasLHS = isLHS;
            if (!isRHS || isLHS) {
                errors.add(KEMException.compilerError("Found #fun expression not on right-hand side of rule.", k));
            }
            if (k.klabel().name().equals("#fun2")) {
                isRHS = true;
                isLHS = true;
                apply(k.items().get(0));
                // in well formed programs this should always reset to true and false, but we want to make sure we don't
                // create spurious reports if this constraint was violated by the user.
                isRHS = wasRHS;
                isLHS = wasLHS;
                apply(k.items().get(1));
            } else {
                isRHS = false;
                isLHS = true;
                apply(k.items().get(0));
                isRHS = true;
                isLHS = false;
                apply(k.items().get(1));
                // in well formed programs this should always reset to true and false, but we want to make sure we don't
                // create spurious reports if this constraint was violated by the user.
                isRHS = wasRHS;
                isLHS = wasLHS;
                apply(k.items().get(2));
            }
        } else {
            super.apply(k);
        }
    }
}
