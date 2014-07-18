// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.ktest;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class RegexStringMatcher implements StringMatcher {

    @Override
    public void matches(String patterns, String actual) throws MatchFailure {
        for (String pattern : patterns.split("\n")) {
            Matcher m = Pattern.compile(pattern).matcher(actual);
            if (!m.find()) {
                throw new MatchFailure(String.format("Expected result to match regular expression:" +
                        "%n%s%n%nbut found:%n%s%n", pattern, actual));
            }
        }
    }
}
