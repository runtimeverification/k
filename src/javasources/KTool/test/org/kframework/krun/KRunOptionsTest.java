package org.kframework.krun;

import static org.junit.Assert.*;

import org.junit.Test;

import com.beust.jcommander.JCommander;

public class KRunOptionsTest {

    @Test
    public void testOn() {
        KRunOptions options = new KRunOptions();
        new JCommander(options, "--statistics", "on", "--log-io", "on", "--io", "on");
        assertTrue(options.experimental.statistics);
        assertTrue(options.experimental.logIO);
        assertTrue(options.io());
    }
    
    @Test
    public void testOff() {
        KRunOptions options = new KRunOptions();
        new JCommander(options, "--statistics", "off", "--log-io", "off", "--io", "off");
        assertFalse(options.experimental.statistics);
        assertFalse(options.experimental.logIO);
        assertFalse(options.io());
    }
    
}
