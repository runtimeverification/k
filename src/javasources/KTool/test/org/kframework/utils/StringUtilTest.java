// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils;


import junit.framework.Assert;
import org.junit.Test;

public class StringUtilTest {
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
    public void testErrors() {
        try {
            String str = String.valueOf(new char[]{400});
            StringUtil.enquoteCString(str);
            throw new AssertionError("An " + IllegalArgumentException.class.getName() + " should have been thrown here.");
        } catch (IllegalArgumentException e) {
            // good
        }
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
}
