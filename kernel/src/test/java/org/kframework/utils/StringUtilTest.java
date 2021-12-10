// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.utils;

import junit.framework.Assert;
import org.junit.Test;
import org.kframework.backend.kore.ModuleToKORE;

import java.util.regex.Pattern;

public class StringUtilTest {

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
    public void decodeKoreString() {
        Assert.assertEquals("_V_9", StringUtil.decodeKoreString("'Unds'V'Unds'9"));
        Assert.assertEquals("?_0", StringUtil.decodeKoreString("'QuesUnds'0"));
        Pattern identChar = Pattern.compile("[A-Za-z0-9\\-]");
        StringBuilder buffer = new StringBuilder();
        StringUtil.encodeStringToAlphanumeric(buffer, "?_0", ModuleToKORE.asciiReadableEncodingKore, identChar, "'");
        Assert.assertEquals("'QuesUnds'0", buffer.toString());
        buffer.setLength(0);
        StringUtil.encodeStringToAlphanumeric(buffer, "_V_9", ModuleToKORE.asciiReadableEncodingKore, identChar, "'");
        Assert.assertEquals("'Unds'V'Unds'9", buffer.toString());
    }

    @Test
    public void testBijection() {
        char[] all = new char[256];
        for (int i = 0; i < 256; i++)
            all[i] = (char) i;
        String str = String.valueOf(all);
        String enquoted = StringUtil.enquoteCString(str);
        String backToAll = StringUtil.unquoteCString(enquoted);
        char[] all2 = backToAll.toCharArray();

        Assert.assertEquals("Different sizes after running quote unquote.", all.length , all2.length);
        for (int i = 0; i < 256; i++)
            Assert.assertEquals("Different values at position: " + i, all[i] , all2[i]);
    }

    @Test
    public void testKBijection() {
        char[] all = new char[257];
        for (int i = 0; i < 256; i++)
            all[i] = (char) i;
        all[256] = 0xffff;
        String str = String.valueOf(all);
        String enquoted = StringUtil.enquoteKString(str);
        String backToAll = StringUtil.unquoteKString(enquoted);
        char[] all2 = backToAll.toCharArray();

        Assert.assertEquals("Different sizes after running quote unquote.", all.length , all2.length);
        for (int i = 0; i < 257; i++)
            Assert.assertEquals("Different values at position: " + i, all[i] , all2[i]);
    }

    @Test
    public void testSplitLine() {
        String longLine = "http://www.kframework.org should be splitted";
        Assert.assertEquals(
                "http://www.kframework.org\nshould be\nsplitted",
                StringUtil.splitLines(longLine, 10));
        Assert.assertEquals(
                "http://www.kframework.org\nshould be splitted",
                StringUtil.splitLines(longLine, 20));
        Assert.assertEquals(
                "http://www.kframework.org\nshould\nbe\nsplitted",
                StringUtil.splitLines(longLine, 0));
        Assert.assertEquals(
                "http://www.kframework.org should be\nsplitted",
                StringUtil.splitLines(longLine, longLine.length()));
        Assert.assertEquals(longLine, StringUtil.splitLines(longLine, longLine.length() + 1));

        String multiLine =
                "http://www.kframework.org\nshort enough line";
        Assert.assertEquals(
                "http://www.kframework.org\nshort enough line",
                StringUtil.splitLines(multiLine, 30));
        Assert.assertEquals(
                "http://www.kframework.org\nshort enough\nline",
                StringUtil.splitLines(multiLine, 13));
        Assert.assertEquals(
                "http://www.kframework.org\nshort\nenough\nline",
                StringUtil.splitLines(multiLine, 10));
    }
}

