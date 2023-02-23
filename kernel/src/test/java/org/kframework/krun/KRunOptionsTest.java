// Copyright (c) K Team. All Rights Reserved.
package org.kframework.krun;

import com.beust.jcommander.JCommander;
import org.junit.Test;

import static org.junit.Assert.*;

public class KRunOptionsTest {

    @Test
    public void testOn() {
        KRunOptions options = new KRunOptions();
        new JCommander(options, "--statistics", "on", "--io", "on");
        assertTrue(options.statistics);
        assertTrue(options.io());
    }

    @Test
    public void testOff() {
        KRunOptions options = new KRunOptions();
        new JCommander(options, "--statistics", "off", "--io", "off");
        assertFalse(options.statistics);
        assertFalse(options.io());
    }

}
