// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.utils;

import javax.annotation.Nonnull;
import java.util.Formatter;

/**
 * An extension of {@code java.util.Formatter} that indents every new line with specified prefix.
 *
 * @author Denis Bogdanas
 * Created on 14-Apr-19.
 */
public class IndentingFormatter {

    public static final String ENDL = "\n";
    private Formatter formatter;
    private String endlReplacement;

    public IndentingFormatter(@Nonnull Formatter formatter, @Nonnull String indent) {
        this.formatter = formatter;
        this.endlReplacement = indent.isEmpty() ? ENDL : ENDL + indent;
    }

    public Formatter format(String format, Object... args) {
        if (endlReplacement.equals(ENDL)) {
            return formatter.format(format, args);
        } else {
            String newFormat = buildNewFormat(format);
            Object[] newArgs = buildNewArgs(args);
            return formatter.format(newFormat, newArgs);
        }
    }

    public String buildNewFormat(String format) {
        return format.replaceAll("\\R", endlReplacement);
    }

    public Object[] buildNewArgs(Object[] args) {
        Object[] newArgs = new Object[args.length];
        for (int i = 0; i < args.length; i++) {
            newArgs[i] = args[i] instanceof String
                         ? ((String) args[i]).replaceAll("\\R", endlReplacement)
                         : args[i];
        }
        return newArgs;
    }
}
