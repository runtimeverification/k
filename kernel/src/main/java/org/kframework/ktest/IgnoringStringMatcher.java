// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.ktest;

public class IgnoringStringMatcher implements StringMatcher {

    private final boolean ignoreWS;
    private final boolean ignoreBalancedParens;

    public IgnoringStringMatcher(boolean ignoreWS, boolean ignoreBalancedParens) {
        this.ignoreWS = ignoreWS;
        this.ignoreBalancedParens = ignoreBalancedParens;
    }

    @Override
    public void matches(final String pattern, final String actual) throws MatchFailure {
        // algorithm copied from old ktest; I'm not convinced that they work correctly in all cases
        String pattern1 = pattern;
        String actual1 = actual;
        if (ignoreWS) {
            pattern1 = pattern1.replaceAll("\\r|\\s|\\n","");
            actual1 = actual1.replaceAll("\\r|\\s|\\n","");
            pattern1 = pattern1.replaceAll("\u001B\\[[;\\d]*m", "");
            actual1 = actual1.replaceAll("\u001B\\[[;\\d]*m", "");
        } else {
            pattern1 = pattern1.replaceAll("\\r","");
            actual1 = actual1.replaceAll("\\r","");
        }
        if (ignoreBalancedParens) {
            pattern1 = removeAllBalanced(pattern1);
            actual1 = removeAllBalanced(actual1);
        }
        if (pattern1.trim().compareTo(actual1.trim()) != 0) {
            throw new StringMatcher.MatchFailure(
                    String.format("Expected:%n%s%n%nbut found:%n%s%n", pattern, actual));
        }
    }

    private static String removeAllBalanced(String s1) {
        String s2 = s1.replaceAll("\\((.*?)\\)", "$1")
                .replaceAll("\\{(.*?)\\}", "$1")
                .replaceAll("\\[(.*?)\\]", "$1");
        if (s1.equals(s2)) {
            return s1;
        } else {
            return removeAllBalanced(s2);
        }
    }
}
