package org.kframework.ktest;

import java.util.Comparator;

public class IgnoringStringComparator implements Comparator<String> {

    private final boolean ignoreWS;
    private final boolean ignoreBalancedParens;

    public IgnoringStringComparator(boolean ignoreWS, boolean ignoreBalancedParens) {
        this.ignoreWS = ignoreWS;
        this.ignoreBalancedParens = ignoreBalancedParens;
    }

    @Override
    public int compare(String s1, String s2) {
        // algorithm copied from old ktest; I'm not convinced that they work correctly in all cases
        if (ignoreWS) {
            s1 = s1.replaceAll("\\r|\\s|\\n","");
            s2 = s2.replaceAll("\\r|\\s|\\n","");
            s1 = s1.replaceAll("\u001B\\[[;\\d]*m", "");
            s2 = s2.replaceAll("\u001B\\[[;\\d]*m", "");
        } else {
            s1 = s1.replaceAll("\\r","");
            s2 = s2.replaceAll("\\r","");
        }
        if (ignoreBalancedParens) {
            s1 = removeAllBalanced(s1);
            s2 = removeAllBalanced(s2);
        }
        return s1.trim().compareTo(s2.trim());
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
