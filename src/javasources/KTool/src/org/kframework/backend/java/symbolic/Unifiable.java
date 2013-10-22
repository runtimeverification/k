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

    public void accept(Unifier unifier, Term patten);

}
