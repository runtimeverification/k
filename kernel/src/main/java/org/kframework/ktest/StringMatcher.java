// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.ktest;

public interface StringMatcher {
    /**
     * Checks whether {@code actual} satisfies the constraint specified by {@code pattern}. Success means
     * the method returns; failure means an exception is thrown.
     *
     * An implementation of this interface may choose any meaning it prefers for how to interpret the
     * {@code pattern}. Thus, from the perspective of this interface, a pattern is an opaque reference
     * to a set of strings that, when passed as the parameter {@code actual}, will return without throwing
     * an exception.
     *
     * @param pattern A implementation-specific representation of a set of strings this matcher matches.
     * @param actual The string being matched against the {@code pattern}.
     * @throws MatchFailure if {@code actual} does not match the {@code pattern}.
     */
    void matches(String pattern, String actual) throws MatchFailure;

    public static class MatchFailure extends Exception {
        public MatchFailure(String message) { super(message); }
    }
}