package org.kframework.ktest;

import java.util.HashSet;
import java.util.Set;

public class QuoteHandling {

    private static final String SINGLE_QUOTE = "\'";
    private static final String DOUBLE_QUOTE = "\"";

    private static Set<String> escapes = new HashSet<>();
    static {
        escapes.add("<");
        escapes.add(">");
    }

    public static String quoteArgument(final String arg) {
        String cleanArg = arg.trim();

        // strip the quotes from both ends
        while ((cleanArg.startsWith(SINGLE_QUOTE) && cleanArg.endsWith(SINGLE_QUOTE))
                || (cleanArg.startsWith(DOUBLE_QUOTE) && cleanArg.endsWith(DOUBLE_QUOTE)))
            cleanArg = cleanArg.substring(1, cleanArg.length() - 1);

        if (cleanArg.contains(DOUBLE_QUOTE)) {
            if (cleanArg.contains(SINGLE_QUOTE))
                throw new IllegalArgumentException(
                        "Can't handle single and double quotes in same argument");
            else
                return String.format("\'%s\'", cleanArg);
        } else if (cleanArg.contains(SINGLE_QUOTE) || cleanArg.contains(" ")) {
            return String.format("\"%s\"", cleanArg);
        } else {
            for (String escape : escapes)
                if (cleanArg.contains(escape))
                    return String.format("\"%s\"", cleanArg);
            return cleanArg;
        }
    }

    public static String[] quoteArguments(final String[] args) {
        String[] ret = args.clone();
        for (int i = 0; i < ret.length; i++)
            ret[i] = quoteArgument(ret[i]);
        return ret;
    }

    /*
    public static void main(String[] args) {
        System.out.println(quoteArgument("test"));
        System.out.println(quoteArgument("test\"test"));
        System.out.println(quoteArgument("test'test"));
        System.out.println(quoteArgument("\"test'test\""));
        System.out.println(quoteArgument("'test\"test'"));
        System.out.println(quoteArgument("<test>"));
        System.out.println(quoteArgument("<test'test>"));
        System.out.println(quoteArgument("<test\"test>"));
    }
    */
}
