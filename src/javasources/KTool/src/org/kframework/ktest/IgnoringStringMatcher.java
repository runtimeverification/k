// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest;

public class IgnoringStringMatcher implements StringMatcher {

    private final boolean ignoreWS;
    private final boolean ignoreBalancedParens;
    
    public IgnoringStringMatcher(boolean ignoreWS, boolean ignoreBalancedParens) {
        this.ignoreWS = ignoreWS;
        this.ignoreBalancedParens = ignoreBalancedParens;
    }

    @Override
    public void matches(String pattern, String actual) throws MatchFailure {
        // algorithm copied from old ktest; I'm not convinced that they work correctly in all cases
        if (ignoreWS) {
            pattern = pattern.replaceAll("\\r|\\s|\\n","");
            actual = actual.replaceAll("\\r|\\s|\\n","");
            pattern = pattern.replaceAll("\u001B\\[[;\\d]*m", "");
            actual = actual.replaceAll("\u001B\\[[;\\d]*m", "");
        } else {
            pattern = pattern.replaceAll("\\r","");
            actual = actual.replaceAll("\\r","");
        }
        if (ignoreBalancedParens) {
            pattern = removeAllBalanced(pattern);
            actual = removeAllBalanced(actual);
        }
        if (pattern.trim().compareTo(actual.trim()) != 0) {
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
