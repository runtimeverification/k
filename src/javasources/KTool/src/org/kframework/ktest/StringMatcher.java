// Copyright (C) 2014 K Team. All Rights Reserved.
package org.kframework.ktest;

public interface StringMatcher {
    boolean matches(String pattern, String actual);
    
    String errorMessage();
}