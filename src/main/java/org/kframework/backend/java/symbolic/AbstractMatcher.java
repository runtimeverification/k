// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Term;

/**
 * @author YilongL
 */
public abstract class AbstractMatcher implements Matcher {

    /**
     * Fails the pattern matching task.
     *
     * @throws PatternMatchingFailure
     */
    protected void fail(Term term, Term otherTerm) {
        throw PatternMatchingFailure.PATTERN_MATCHING_FAILURE;
    }
}
