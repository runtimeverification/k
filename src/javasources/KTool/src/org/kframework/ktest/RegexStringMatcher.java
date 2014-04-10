// Copyright (C) 2014 K Team. All Rights Reserved.
package org.kframework.ktest;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class RegexStringMatcher implements StringMatcher {

    private String failedRegex;
    private String failedActual;
    
    @Override
    public boolean matches(String patterns, String actual) {
        boolean matches = true;
        for (String pattern : patterns.split("\n")) {
            Matcher m = Pattern.compile(pattern).matcher(actual);
            matches &= m.find();
            if (!matches) {
                failedRegex = pattern;
                failedActual = actual;
                break;
            }
        }
        return matches;
    }
    
    @Override
    public String errorMessage() {
        return String.format("Expected result to match regular expression:%n%s%n%nbut found:%n%s%n", failedRegex, failedActual);
    }

}
