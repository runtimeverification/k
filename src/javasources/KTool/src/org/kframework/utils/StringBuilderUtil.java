// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.utils;

/**
 * @author Denis Bogdanas
 *         Date: 10/26/13
 */
public class StringBuilderUtil {
    public static void replaceAll(StringBuilder builder, String from, String to)
    {
        int index = builder.indexOf(from);
        while (index != -1)
        {
            builder.replace(index, index + from.length(), to);
            index += to.length(); // Move to the end of the replacement
            index = builder.indexOf(from, index);
        }
    }

    public static void replaceFirst(StringBuilder builder, String from, String to)
    {
        int index = builder.indexOf(from);
        if (index != -1) {
            builder.replace(index, index + from.length(), to);
        }
    }
}
