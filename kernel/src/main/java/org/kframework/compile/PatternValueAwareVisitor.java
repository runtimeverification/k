// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.kore.KApply;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;

/**
 * A visitor designed to track whether we are currently in Pattern or Value position.
 *
 * outside of rewrite = LHS&RHS, value&pattern
 * lhs of rewrite     = LHS, pattern
 * rhs of rewrite     = RHS, value
 * requires           = LHS, value
 * ensures            = RHS, value
 */
public class PatternValueAwareVisitor extends VisitK {

    private final Set<KEMException> errors;
    public PatternValueAwareVisitor(boolean isBody, Set<KEMException> errors) {
        this.errors = errors;
        if (isBody) {
            isValue = true;
            isPattern = true;
        } else {
            isValue = true;
            isPattern = false;
        }
    }


    private boolean isPattern;
    private boolean isValue;

    @Override
    public void apply(KRewrite k) {
        isValue = false;
        apply(k.left());
        isValue = true;
        isPattern = false;
        apply(k.right());
        isPattern = true;
    }

    @Override
    public void apply(KApply k) {
        if (!(k.klabel() instanceof KVariable) && k.klabel().name().equals("#fun2") || k.klabel().name().equals("#fun3") || k.klabel().name().equals("#let")) {
            boolean wasValue = isValue;
            boolean wasPattern = isPattern;
            if (isPattern) {
                errors.add(KEMException.compilerError("Found #fun expression in a pattern location (LHS and outside of rewrite).", k));
            }
            if (k.klabel().name().equals("#fun2")) {
                isValue = true;
                isPattern = true;
                apply(k.items().get(0));
                // in well formed programs this should always reset to true and false, but we want to make sure we don't
                // create spurious reports if this constraint was violated by the user.
                isValue = wasValue;
                isPattern = wasPattern;
                apply(k.items().get(1));
            } else {
                isPattern = true;
                isValue = false;
                apply(k.items().get(0));
                isPattern = false;
                isValue = true;
                apply(k.items().get(1));
                // in well formed programs this should always reset to true and false, but we want to make sure we don't
                // create spurious reports if this constraint was violated by the user.
                isValue = wasValue;
                isPattern = wasPattern;
                apply(k.items().get(2));
            }
        } else {
            super.apply(k);
        }
    }

    public boolean isPattern() {
        return isPattern;
    }

    public boolean isValue() {
        return isValue;
    }
}
