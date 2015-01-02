// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Term;


/**
 * Implements a visitor pattern specialized for unification.
 *
 * @see Unifier
 *
 * @author AndreiS
 */
public interface Unifiable {

    /**
     * Class listed in the {@code Unifier} should implement this method to accept
     * the given unifier; otherwise, it should throw an
     * {@code UnsupportedOperationException}.
     *
     * @param unifier
     * @param pattern
     */
    public void accept(Unifier unifier, Term pattern);

}
