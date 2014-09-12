// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

/**
 * Efficient exception with no stacktrace; used for flow-control in the
 * {@link PatternMatcher}.
 *
 * @author YilongL
 *
 */
public class PatternMatchingFailure extends UnificationOrMatchingFailure {

    public static final PatternMatchingFailure PATTERN_MATCHING_FAILURE = new PatternMatchingFailure("pattern matching failed");

    private PatternMatchingFailure(String message) {
        super(message);
    }
}