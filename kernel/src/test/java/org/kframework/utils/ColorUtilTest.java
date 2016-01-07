// Copyright (c) 2014-2016 K Team. All Rights Reserved.
package org.kframework.utils;

import org.junit.Test;
import org.kframework.krun.ColorSetting;

import static org.junit.Assert.*;

public class ColorUtilTest {

    @Test
    public void testGetColor() {
        // set java.awt.headless so that we don't activate the awt bug (see issue #982)
        System.setProperty("java.awt.headless", "true");
        assertEquals("", ColorUtil.RgbToAnsi("red", ColorSetting.OFF, "black"));
        assertEquals("\u001b[31m", ColorUtil.RgbToAnsi("red", ColorSetting.ON, "black"));
        assertEquals("", ColorUtil.RgbToAnsi("red", ColorSetting.OFF, "red"));
    }
}
