// Copyright (c) 2013-2014 K Team. All Rights Reserved.
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

    public void accept(Unifier unifier, Term pattern);

}
