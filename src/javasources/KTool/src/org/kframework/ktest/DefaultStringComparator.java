package org.kframework.ktest;

import java.util.Comparator;

public class DefaultStringComparator implements Comparator<String> {
    @Override
    public int compare(String s1, String s2) {
        return s1.replaceAll("\\r", "").compareTo(s2.replaceAll("\\r", ""));
    }
}
