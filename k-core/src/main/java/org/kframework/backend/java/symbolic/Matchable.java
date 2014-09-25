// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Term;


/**
 * Implements a visitor pattern specialized for pattern matching.
 *
 * @see Matcher
 *
 * @author YilongL
 */
public interface Matchable {

    public void accept(Matcher matcher, Term pattern);

}
