// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Term;


/**
 * @author AndreiS
 */
public abstract class AbstractUnifier implements Unifier {
    /**
     * Left-hand side of a minimal equality causing this unification to fail.
     * Must be set if this unification fails.
     */
    private Term unificationFailureLeftHandSide;
    /**
     * Right-hand side of a minimal equality causing this unification to fail.
     * Must be set if this unification fails.
     */
    private Term unificationFailureRightHandSide;

    public Term unificationFailureLeftHandSide() {
        return unificationFailureLeftHandSide;
    }

    public Term unificationFailureRightHandSide() {
        return unificationFailureRightHandSide;
    }

    /**
     * Fails the unification task.
     *
     * @throws UnificationFailure
     */
    protected void fail(Term term, Term otherTerm) {
        unificationFailureLeftHandSide = term;
        unificationFailureRightHandSide = otherTerm;
        throw UnificationFailure.UNIFICATION_FAILURE;
    }
}