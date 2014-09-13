// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils;

import static org.junit.Assert.*;

import java.awt.Color;

import org.junit.Test;
import org.kframework.krun.ColorSetting;

public class ColorUtilTest {

    @Test
    public void testGetColor() {
        assertEquals("", ColorUtil.RgbToAnsi(Color.RED, ColorSetting.OFF, Color.BLACK));
        assertEquals("\u001b[31m", ColorUtil.RgbToAnsi(Color.RED, ColorSetting.ON, Color.BLACK));
        assertEquals("", ColorUtil.RgbToAnsi(Color.RED, ColorSetting.OFF, Color.RED));
    }
}
