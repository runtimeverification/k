// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils;

import static org.junit.Assert.*;

import org.junit.Test;
import org.kframework.unparser.ColorSetting;

public class ColorUtilTest {

  @Test
  public void testGetColor() {
    // set java.awt.headless so that we don't activate the awt bug (see issue #982)
    System.setProperty("java.awt.headless", "true");
    assertEquals("", ColorUtil.RgbToAnsi("red", ColorSetting.OFF));
    assertEquals("\u001b[31m", ColorUtil.RgbToAnsi("red", ColorSetting.ON));
  }
}
