package org.kframework.backend.java.util;

import org.kframework.backend.java.kil.ConstrainedTerm;


/**
 * Class grouping various useful constants and static methods.
 *
 * @author AndreiS
 */
public class Utils {

    public static final int HASH_PRIME = 47;

    /**
     * Static counter that records the number of invocations of the method
     * {@link ConstrainedTerm#unify(ConstrainedTerm)}.
     */
    public static int constrainedTermUnifyInvocationCounter = 0;
}
