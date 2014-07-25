// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils;

import junit.framework.Assert;
import org.junit.Test;

public class UtilsTest {

    @Test
    public void StringUtilUnquote() throws Exception {
        Assert.assertTrue(StringUtil.unquoteKString("\"\\n\"").equals("\n"));
        Assert.assertTrue(StringUtil.unquoteKString("\"\\r\"").equals("\r"));
        Assert.assertTrue(StringUtil.unquoteKString("\"\\f\"").equals("\f"));
        Assert.assertTrue(StringUtil.unquoteKString("\"\\t\"").equals("\t"));

        Assert.assertTrue(StringUtil.unquoteKString("\"\\x20\"").equals(" "));
        Assert.assertTrue(StringUtil.unquoteKString("\"\\u0020\"").equals(" "));
        Assert.assertTrue(StringUtil.unquoteKString("\"\\U00000020\"").equals(" "));

        Assert.assertTrue(StringUtil.unquoteKString("\"\\U00000020\"").equals(" "));

        try {
            StringUtil.unquoteKString("\"\\U00110000\"");
            throw new AssertionError();
        } catch (IllegalArgumentException e) {
        }
        try {
            StringUtil.unquoteKString("\"\\U0000d801\"");
            throw new AssertionError();
        } catch (IllegalArgumentException e) {
        }
    }

    @Test
    public void StringUtilEscapeShell() throws Exception {
        String[] cmd1 = new String[] {"foo", "bar \" baz"};
        String[] cmd2 = new String[] {"'"};
        Assert.assertEquals("\"foo\" \"bar \\\" baz\"", StringUtil.escapeShell(cmd1, OS.WIN));
        Assert.assertEquals("'foo' 'bar \" baz'", StringUtil.escapeShell(cmd1, OS.UNIX));
        Assert.assertEquals("''\\'''", StringUtil.escapeShell(cmd2, OS.UNIX));
    }
}
