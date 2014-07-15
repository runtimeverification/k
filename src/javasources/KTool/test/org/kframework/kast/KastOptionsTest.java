// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kast;

import static org.junit.Assert.*;

import java.io.File;

import org.junit.Test;

import com.beust.jcommander.JCommander;

public class KastOptionsTest {

    @Test
    public void testReadDefinition() {
        KastOptions options = new KastOptions();
        new JCommander(options, "--directory", "share/test-files");
        assertEquals(new File("share/test-files/test-kompiled"), options.definition());
        assertTrue(options.definition().exists());
        assertTrue(options.definition().isDirectory());
    }
}
