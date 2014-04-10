package org.kframework.ktest;

public interface StringMatcher {
    boolean matches(String pattern, String actual);
    
    String errorMessage();
}