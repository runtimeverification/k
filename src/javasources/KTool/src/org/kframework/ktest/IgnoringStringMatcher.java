// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest;

public class IgnoringStringMatcher implements StringMatcher {

    private final boolean ignoreWS;
    private final boolean ignoreBalancedParens;

    private String lastPattern;
    private String lastActual;
    
    public IgnoringStringMatcher(boolean ignoreWS, boolean ignoreBalancedParens) {
        this.ignoreWS = ignoreWS;
        this.ignoreBalancedParens = ignoreBalancedParens;
    }

    @Override
    public boolean matches(String pattern, String actual) {
        lastPattern = pattern;
        lastActual = actual;
        
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
        return pattern.trim().compareTo(actual.trim()) == 0;
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
    
    @Override
    public String errorMessage() {
        return String.format("Expected:%n%s%n%nbut found:%n%s%n", lastPattern, lastActual);
    }

}
